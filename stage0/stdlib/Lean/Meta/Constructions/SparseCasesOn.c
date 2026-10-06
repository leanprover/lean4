// Lean compiler output
// Module: Lean.Meta.Constructions.SparseCasesOn
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.Constructions.CtorIdx import Lean.Meta.HasNotBit import Lean.Meta.Transform
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_Lean_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkHasNotBit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SparseCasesOn"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 142, 211, 52, 27, 176, 89, 6)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(93, 38, 184, 128, 76, 32, 215, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 79, 91, 86, 222, 171, 161, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 83, 47, 52, 170, 238, 223, 102)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "sparseCasesOnCacheExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 173, 73, 104, 127, 128, 171, 122)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
static const lean_array_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sparseCasesOnInfoExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 231, 162, 79, 58, 254, 239, 178)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.Constructions.SparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.mkSparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "sparse `casesOn` for `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is already registered as `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 140, 41, 106, 106, 114, 66, 206)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value;
static const lean_array_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "mkSparseCasesOn: unexpected number of parameters in type of `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "mkSparseCasesOn: constructor "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " is not a constructor of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__0;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "mkSparseCasesOn: unexpected number of universe parameters in `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__2;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__3;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "_sparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(111, 99, 43, 146, 60, 255, 155, 135)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__5 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__5_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "mkSparseCasesOn: requested casesOn combinator is not sparse"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__6 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_3_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_3_, v_one_6_);
lean_dec(v_x_3_);
v___x_8_ = lean_array_fget_borrowed(v_xs_1_, v_n_7_);
v___x_9_ = lean_array_fget_borrowed(v_ys_2_, v_n_7_);
v___x_10_ = lean_name_eq(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
lean_dec(v_n_7_);
return v___x_10_;
}
else
{
v_x_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object* v_xs_12_, lean_object* v_ys_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_12_, v_ys_13_, v_x_14_);
lean_dec_ref(v_ys_13_);
lean_dec_ref(v_xs_12_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_indName_19_; lean_object* v_ctors_20_; uint8_t v_isPrivate_21_; lean_object* v_indName_22_; lean_object* v_ctors_23_; uint8_t v_isPrivate_24_; uint8_t v___x_25_; 
v_indName_19_ = lean_ctor_get(v_x_17_, 0);
v_ctors_20_ = lean_ctor_get(v_x_17_, 1);
v_isPrivate_21_ = lean_ctor_get_uint8(v_x_17_, sizeof(void*)*2);
v_indName_22_ = lean_ctor_get(v_x_18_, 0);
v_ctors_23_ = lean_ctor_get(v_x_18_, 1);
v_isPrivate_24_ = lean_ctor_get_uint8(v_x_18_, sizeof(void*)*2);
v___x_25_ = lean_name_eq(v_indName_19_, v_indName_22_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_array_get_size(v_ctors_20_);
v___x_27_ = lean_array_get_size(v_ctors_23_);
v___x_28_ = lean_nat_dec_eq(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_ctors_20_, v_ctors_23_, v___x_26_);
if (v___x_29_ == 0)
{
return v___x_29_;
}
else
{
if (v_isPrivate_24_ == 0)
{
if (v_isPrivate_21_ == 0)
{
return v___x_29_;
}
else
{
return v_isPrivate_24_;
}
}
else
{
return v_isPrivate_21_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_30_, v_x_31_);
lean_dec_ref(v_x_31_);
lean_dec_ref(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object* v_xs_34_, lean_object* v_ys_35_, lean_object* v_hsz_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_34_, v_ys_35_, v_x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object* v_xs_40_, lean_object* v_ys_41_, lean_object* v_hsz_42_, lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(v_xs_40_, v_ys_41_, v_hsz_42_, v_x_43_, v_x_44_);
lean_dec_ref(v_ys_41_);
lean_dec_ref(v_xs_40_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object* v_as_49_, size_t v_i_50_, size_t v_stop_51_, uint64_t v_b_52_){
_start:
{
uint64_t v___y_54_; uint8_t v___x_59_; 
v___x_59_ = lean_usize_dec_eq(v_i_50_, v_stop_51_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = lean_array_uget_borrowed(v_as_49_, v_i_50_);
if (lean_obj_tag(v___x_60_) == 0)
{
uint64_t v___x_61_; 
v___x_61_ = 1723ULL;
v___y_54_ = v___x_61_;
goto v___jp_53_;
}
else
{
uint64_t v_hash_62_; 
v_hash_62_ = lean_ctor_get_uint64(v___x_60_, sizeof(void*)*2);
v___y_54_ = v_hash_62_;
goto v___jp_53_;
}
}
else
{
return v_b_52_;
}
v___jp_53_:
{
uint64_t v___x_55_; size_t v___x_56_; size_t v___x_57_; 
v___x_55_ = lean_uint64_mix_hash(v_b_52_, v___y_54_);
v___x_56_ = ((size_t)1ULL);
v___x_57_ = lean_usize_add(v_i_50_, v___x_56_);
v_i_50_ = v___x_57_;
v_b_52_ = v___x_55_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_){
_start:
{
size_t v_i_boxed_67_; size_t v_stop_boxed_68_; uint64_t v_b_boxed_69_; uint64_t v_res_70_; lean_object* v_r_71_; 
v_i_boxed_67_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_b_boxed_69_ = lean_unbox_uint64(v_b_66_);
lean_dec_ref(v_b_66_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_as_63_, v_i_boxed_67_, v_stop_boxed_68_, v_b_boxed_69_);
lean_dec_ref(v_as_63_);
v_r_71_ = lean_box_uint64(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object* v_x_72_){
_start:
{
lean_object* v_indName_73_; lean_object* v_ctors_74_; uint8_t v_isPrivate_75_; uint64_t v___y_77_; uint64_t v___y_78_; uint64_t v___x_84_; uint64_t v___y_86_; 
v_indName_73_ = lean_ctor_get(v_x_72_, 0);
v_ctors_74_ = lean_ctor_get(v_x_72_, 1);
v_isPrivate_75_ = lean_ctor_get_uint8(v_x_72_, sizeof(void*)*2);
v___x_84_ = 0ULL;
if (lean_obj_tag(v_indName_73_) == 0)
{
uint64_t v___x_95_; 
v___x_95_ = 1723ULL;
v___y_86_ = v___x_95_;
goto v___jp_85_;
}
else
{
uint64_t v_hash_96_; 
v_hash_96_ = lean_ctor_get_uint64(v_indName_73_, sizeof(void*)*2);
v___y_86_ = v_hash_96_;
goto v___jp_85_;
}
v___jp_76_:
{
uint64_t v___x_79_; 
v___x_79_ = lean_uint64_mix_hash(v___y_77_, v___y_78_);
if (v_isPrivate_75_ == 0)
{
uint64_t v___x_80_; uint64_t v___x_81_; 
v___x_80_ = 13ULL;
v___x_81_ = lean_uint64_mix_hash(v___x_79_, v___x_80_);
return v___x_81_;
}
else
{
uint64_t v___x_82_; uint64_t v___x_83_; 
v___x_82_ = 11ULL;
v___x_83_ = lean_uint64_mix_hash(v___x_79_, v___x_82_);
return v___x_83_;
}
}
v___jp_85_:
{
uint64_t v___x_87_; uint64_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_87_ = lean_uint64_mix_hash(v___x_84_, v___y_86_);
v___x_88_ = 7ULL;
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_array_get_size(v_ctors_74_);
v___x_91_ = lean_nat_dec_lt(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
v___y_77_ = v___x_87_;
v___y_78_ = v___x_88_;
goto v___jp_76_;
}
else
{
size_t v___x_92_; size_t v___x_93_; uint64_t v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_90_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_74_, v___x_92_, v___x_93_, v___x_88_);
v___y_77_ = v___x_87_;
v___y_78_ = v___x_94_;
goto v___jp_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object* v_x_97_){
_start:
{
uint64_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_97_);
lean_dec_ref(v_x_97_);
v_r_99_ = lean_box_uint64(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(lean_object* v___x_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object* v___x_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(v___x_105_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___f_112_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; 
v___f_147_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_box(1);
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_));
v___x_151_ = 0;
v___x_152_ = 1;
v___x_153_ = l_Lean_registerEnvExtension___redArg(v___f_147_, v___x_148_, v___x_149_, v___x_150_, v___x_151_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
return v_res_155_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_164_, lean_object* v_n_165_, lean_object* v_x_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Lean_Environment_hasExposedBody(v_env_164_, v_n_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_env_168_, lean_object* v_n_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(v_env_168_, v_n_169_, v_x_170_);
lean_dec_ref(v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v_k_175_; lean_object* v_v_176_; lean_object* v_l_177_; lean_object* v_r_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_k_175_ = lean_ctor_get(v_x_174_, 1);
v_v_176_ = lean_ctor_get(v_x_174_, 2);
v_l_177_ = lean_ctor_get(v_x_174_, 3);
v_r_178_ = lean_ctor_get(v_x_174_, 4);
v___x_179_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_173_, v_l_177_);
lean_inc(v_v_176_);
lean_inc(v_k_175_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_k_175_);
lean_ctor_set(v___x_180_, 1, v_v_176_);
v___x_181_ = lean_array_push(v___x_179_, v___x_180_);
v_init_173_ = v___x_181_;
v_x_174_ = v_r_178_;
goto _start;
}
else
{
return v_init_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_183_, lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_183_, v_x_184_);
lean_dec(v_x_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_188_, lean_object* v_s_189_){
_start:
{
lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v_all_192_; lean_object* v___x_193_; lean_object* v_exported_194_; lean_object* v___x_195_; 
v___f_190_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_190_, 0, v_env_188_);
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v_all_192_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_191_, v_s_189_);
v___x_193_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_190_, v_s_189_);
v_exported_194_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_191_, v___x_193_);
lean_dec(v___x_193_);
lean_inc_ref(v_exported_194_);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v_exported_194_);
lean_ctor_set(v___x_195_, 1, v_exported_194_);
lean_ctor_set(v___x_195_, 2, v_all_192_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; 
v___f_204_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_207_ = 0;
v___x_208_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_205_, v___x_206_, v___x_207_, v___f_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object* v_init_211_, lean_object* v_t_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_211_, v_t_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_214_, lean_object* v_t_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(v_init_214_, v_t_215_);
lean_dec(v_t_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object* v_kind_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v_auxDeclNGen_221_; lean_object* v___x_222_; lean_object* v_env_223_; lean_object* v___x_224_; lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; lean_object* v_env_228_; lean_object* v_nextMacroScope_229_; lean_object* v_ngen_230_; lean_object* v_traceState_231_; lean_object* v_cache_232_; lean_object* v_recordedDeps_233_; lean_object* v_messages_234_; lean_object* v_infoState_235_; lean_object* v_snapshotTasks_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_245_; 
v___x_220_ = lean_st_ref_get(v___y_218_);
v_auxDeclNGen_221_ = lean_ctor_get(v___x_220_, 3);
lean_inc_ref(v_auxDeclNGen_221_);
lean_dec(v___x_220_);
v___x_222_ = lean_st_ref_get(v___y_218_);
v_env_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_env_223_);
lean_dec(v___x_222_);
v___x_224_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_223_, v_auxDeclNGen_221_, v_kind_217_);
v_fst_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_fst_225_);
v_snd_226_ = lean_ctor_get(v___x_224_, 1);
lean_inc(v_snd_226_);
lean_dec_ref(v___x_224_);
v___x_227_ = lean_st_ref_take(v___y_218_);
v_env_228_ = lean_ctor_get(v___x_227_, 0);
v_nextMacroScope_229_ = lean_ctor_get(v___x_227_, 1);
v_ngen_230_ = lean_ctor_get(v___x_227_, 2);
v_traceState_231_ = lean_ctor_get(v___x_227_, 4);
v_cache_232_ = lean_ctor_get(v___x_227_, 5);
v_recordedDeps_233_ = lean_ctor_get(v___x_227_, 6);
v_messages_234_ = lean_ctor_get(v___x_227_, 7);
v_infoState_235_ = lean_ctor_get(v___x_227_, 8);
v_snapshotTasks_236_ = lean_ctor_get(v___x_227_, 9);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_227_, 3);
lean_dec(v_unused_246_);
v___x_238_ = v___x_227_;
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_snapshotTasks_236_);
lean_inc(v_infoState_235_);
lean_inc(v_messages_234_);
lean_inc(v_recordedDeps_233_);
lean_inc(v_cache_232_);
lean_inc(v_traceState_231_);
lean_inc(v_ngen_230_);
lean_inc(v_nextMacroScope_229_);
lean_inc(v_env_228_);
lean_dec(v___x_227_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 3, v_snd_226_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_env_228_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_nextMacroScope_229_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_ngen_230_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v_snd_226_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v_traceState_231_);
lean_ctor_set(v_reuseFailAlloc_244_, 5, v_cache_232_);
lean_ctor_set(v_reuseFailAlloc_244_, 6, v_recordedDeps_233_);
lean_ctor_set(v_reuseFailAlloc_244_, 7, v_messages_234_);
lean_ctor_set(v_reuseFailAlloc_244_, 8, v_infoState_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 9, v_snapshotTasks_236_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_st_ref_put(v___y_218_, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_fst_225_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object* v_kind_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object* v_kind_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_251_, v___y_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object* v_kind_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(v_kind_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object* v_s_265_, lean_object* v_msg_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_panic_fn_borrowed(v_s_265_, v_msg_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object* v_s_268_, lean_object* v_msg_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_s_268_, v_msg_269_);
lean_dec_ref(v_s_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(lean_object* v_k_271_, lean_object* v_b_272_, lean_object* v_c_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc(v___y_275_);
lean_inc_ref(v___y_274_);
v___x_279_ = lean_apply_7(v_k_271_, v_b_272_, v_c_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, lean_box(0));
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed(lean_object* v_k_280_, lean_object* v_b_281_, lean_object* v_c_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(v_k_280_, v_b_281_, v_c_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(lean_object* v_type_289_, lean_object* v_k_290_, uint8_t v_cleanupAnnotations_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___f_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___f_297_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_297_, 0, v_k_290_);
v___x_298_ = 0;
v___x_299_ = lean_box(0);
v___x_300_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_298_, v___x_299_, v_type_289_, v___f_297_, v_cleanupAnnotations_291_, v___x_298_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_300_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_300_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___boxed(lean_object* v_type_317_, lean_object* v_k_318_, lean_object* v_cleanupAnnotations_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_325_; lean_object* v_res_326_; 
v_cleanupAnnotations_boxed_325_ = lean_unbox(v_cleanupAnnotations_319_);
v_res_326_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_type_317_, v_k_318_, v_cleanupAnnotations_boxed_325_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object* v_00_u03b1_327_, lean_object* v_type_328_, lean_object* v_k_329_, uint8_t v_cleanupAnnotations_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_type_328_, v_k_329_, v_cleanupAnnotations_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object* v_00_u03b1_337_, lean_object* v_type_338_, lean_object* v_k_339_, lean_object* v_cleanupAnnotations_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_346_; lean_object* v_res_347_; 
v_cleanupAnnotations_boxed_346_ = lean_unbox(v_cleanupAnnotations_340_);
v_res_347_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_00_u03b1_337_, v_type_338_, v_k_339_, v_cleanupAnnotations_boxed_346_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(lean_object* v_name_348_, lean_object* v_levelParams_349_, lean_object* v_type_350_, lean_object* v_value_351_, lean_object* v_hints_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; uint8_t v___y_357_; uint8_t v___y_364_; lean_object* v_env_367_; uint8_t v___x_368_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_env_367_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref_n(v_env_367_, 2);
lean_dec(v___x_355_);
v___x_368_ = l_Lean_Environment_hasUnsafe(v_env_367_, v_type_350_);
if (v___x_368_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = l_Lean_Environment_hasUnsafe(v_env_367_, v_value_351_);
v___y_364_ = v___x_369_;
goto v___jp_363_;
}
else
{
lean_dec_ref(v_env_367_);
v___y_364_ = v___x_368_;
goto v___jp_363_;
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_inc(v_name_348_);
v___x_358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_358_, 0, v_name_348_);
lean_ctor_set(v___x_358_, 1, v_levelParams_349_);
lean_ctor_set(v___x_358_, 2, v_type_350_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v_name_348_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v_value_351_);
lean_ctor_set(v___x_361_, 2, v_hints_352_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*4, v___y_357_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
v___jp_363_:
{
if (v___y_364_ == 0)
{
uint8_t v___x_365_; 
v___x_365_ = 1;
v___y_357_ = v___x_365_;
goto v___jp_356_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = 0;
v___y_357_ = v___x_366_;
goto v___jp_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg___boxed(lean_object* v_name_370_, lean_object* v_levelParams_371_, lean_object* v_type_372_, lean_object* v_value_373_, lean_object* v_hints_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v_name_370_, v_levelParams_371_, v_type_372_, v_value_373_, v_hints_374_, v___y_375_);
lean_dec(v___y_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object* v_name_378_, lean_object* v_levelParams_379_, lean_object* v_type_380_, lean_object* v_value_381_, lean_object* v_hints_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v_name_378_, v_levelParams_379_, v_type_380_, v_value_381_, v_hints_382_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object* v_name_389_, lean_object* v_levelParams_390_, lean_object* v_type_391_, lean_object* v_value_392_, lean_object* v_hints_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(v_name_389_, v_levelParams_390_, v_type_391_, v_value_392_, v_hints_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_17664__overap_408_; lean_object* v___x_409_; 
v___f_407_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0));
v___x_17664__overap_408_ = lean_panic_fn_borrowed(v___f_407_, v_msg_401_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_409_ = lean_apply_5(v___x_17664__overap_408_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, lean_box(0));
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
lean_object* v_ks_421_; lean_object* v_vs_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_446_; 
v_ks_421_ = lean_ctor_get(v_x_417_, 0);
v_vs_422_ = lean_ctor_get(v_x_417_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_417_);
if (v_isSharedCheck_446_ == 0)
{
v___x_424_ = v_x_417_;
v_isShared_425_ = v_isSharedCheck_446_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_vs_422_);
lean_inc(v_ks_421_);
lean_dec(v_x_417_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_446_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_array_get_size(v_ks_421_);
v___x_427_ = lean_nat_dec_lt(v_x_418_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec(v_x_418_);
v___x_428_ = lean_array_push(v_ks_421_, v_x_419_);
v___x_429_ = lean_array_push(v_vs_422_, v_x_420_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_429_);
lean_ctor_set(v___x_424_, 0, v___x_428_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
else
{
lean_object* v_k_x27_433_; uint8_t v___x_434_; 
v_k_x27_433_ = lean_array_fget_borrowed(v_ks_421_, v_x_418_);
v___x_434_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_419_, v_k_x27_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_436_; 
if (v_isShared_425_ == 0)
{
v___x_436_ = v___x_424_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_ks_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_vs_422_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_x_418_, v___x_437_);
lean_dec(v_x_418_);
v_x_417_ = v___x_436_;
v_x_418_ = v___x_438_;
goto _start;
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = lean_array_fset(v_ks_421_, v_x_418_, v_x_419_);
v___x_442_ = lean_array_fset(v_vs_422_, v_x_418_, v_x_420_);
lean_dec(v_x_418_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_442_);
lean_ctor_set(v___x_424_, 0, v___x_441_);
v___x_444_ = v___x_424_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(lean_object* v_n_447_, lean_object* v_k_448_, lean_object* v_v_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(v_n_447_, v___x_450_, v_k_448_, v_v_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object* v_x_453_, size_t v_x_454_, size_t v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v_es_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v_j_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_es_458_ = lean_ctor_get(v_x_453_, 0);
v___x_459_ = ((size_t)31ULL);
v___x_460_ = lean_usize_land(v_x_454_, v___x_459_);
v_j_461_ = lean_usize_to_nat(v___x_460_);
v___x_462_ = lean_array_get_size(v_es_458_);
v___x_463_ = lean_nat_dec_lt(v_j_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec(v_j_461_);
lean_dec(v_x_457_);
lean_dec_ref(v_x_456_);
return v_x_453_;
}
else
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_502_; 
lean_inc_ref(v_es_458_);
v_isSharedCheck_502_ = !lean_is_exclusive(v_x_453_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_x_453_, 0);
lean_dec(v_unused_503_);
v___x_465_ = v_x_453_;
v_isShared_466_ = v_isSharedCheck_502_;
goto v_resetjp_464_;
}
else
{
lean_dec(v_x_453_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_502_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_v_467_; lean_object* v___x_468_; lean_object* v_xs_x27_469_; lean_object* v___y_471_; 
v_v_467_ = lean_array_fget(v_es_458_, v_j_461_);
v___x_468_ = lean_box(0);
v_xs_x27_469_ = lean_array_fset(v_es_458_, v_j_461_, v___x_468_);
switch(lean_obj_tag(v_v_467_))
{
case 0:
{
lean_object* v_key_476_; lean_object* v_val_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_key_476_ = lean_ctor_get(v_v_467_, 0);
v_val_477_ = lean_ctor_get(v_v_467_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_v_467_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v_v_467_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_val_477_);
lean_inc(v_key_476_);
lean_dec(v_v_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint8_t v___x_481_; 
v___x_481_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_456_, v_key_476_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_del_object(v___x_479_);
v___x_482_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_476_, v_val_477_, v_x_456_, v_x_457_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___y_471_ = v___x_483_;
goto v___jp_470_;
}
else
{
lean_object* v___x_485_; 
lean_dec(v_val_477_);
lean_dec(v_key_476_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v_x_457_);
lean_ctor_set(v___x_479_, 0, v_x_456_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_x_456_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_x_457_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
v___y_471_ = v___x_485_;
goto v___jp_470_;
}
}
}
}
case 1:
{
lean_object* v_node_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_500_; 
v_node_488_ = lean_ctor_get(v_v_467_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_v_467_);
if (v_isSharedCheck_500_ == 0)
{
v___x_490_ = v_v_467_;
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_node_488_);
lean_dec(v_v_467_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_492_ = ((size_t)5ULL);
v___x_493_ = lean_usize_shift_right(v_x_454_, v___x_492_);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_x_455_, v___x_494_);
v___x_496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_node_488_, v___x_493_, v___x_495_, v_x_456_, v_x_457_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_496_);
v___x_498_ = v___x_490_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
v___y_471_ = v___x_498_;
goto v___jp_470_;
}
}
}
default: 
{
lean_object* v___x_501_; 
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_x_456_);
lean_ctor_set(v___x_501_, 1, v_x_457_);
v___y_471_ = v___x_501_;
goto v___jp_470_;
}
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_array_fset(v_xs_x27_469_, v_j_461_, v___y_471_);
lean_dec(v_j_461_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_472_);
v___x_474_ = v___x_465_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v_ks_504_; lean_object* v_vs_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_523_; 
v_ks_504_ = lean_ctor_get(v_x_453_, 0);
v_vs_505_ = lean_ctor_get(v_x_453_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_453_);
if (v_isSharedCheck_523_ == 0)
{
v___x_507_ = v_x_453_;
v_isShared_508_ = v_isSharedCheck_523_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_vs_505_);
lean_inc(v_ks_504_);
lean_dec(v_x_453_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_523_;
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
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_ks_504_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_vs_505_);
v___x_510_ = v_reuseFailAlloc_522_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v_newNode_511_; size_t v___x_512_; uint8_t v___x_513_; 
v_newNode_511_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v___x_510_, v_x_456_, v_x_457_);
v___x_512_ = ((size_t)7ULL);
v___x_513_ = lean_usize_dec_le(v___x_512_, v_x_455_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_514_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_511_);
v___x_515_ = lean_unsigned_to_nat(4u);
v___x_516_ = lean_nat_dec_lt(v___x_514_, v___x_515_);
lean_dec(v___x_514_);
if (v___x_516_ == 0)
{
lean_object* v_ks_517_; lean_object* v_vs_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_ks_517_ = lean_ctor_get(v_newNode_511_, 0);
lean_inc_ref(v_ks_517_);
v_vs_518_ = lean_ctor_get(v_newNode_511_, 1);
lean_inc_ref(v_vs_518_);
lean_dec_ref(v_newNode_511_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0);
v___x_521_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_x_455_, v_ks_517_, v_vs_518_, v___x_519_, v___x_520_);
lean_dec_ref(v_vs_518_);
lean_dec_ref(v_ks_517_);
return v___x_521_;
}
else
{
return v_newNode_511_;
}
}
else
{
return v_newNode_511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(size_t v_depth_524_, lean_object* v_keys_525_, lean_object* v_vals_526_, lean_object* v_i_527_, lean_object* v_entries_528_){
_start:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_get_size(v_keys_525_);
v___x_530_ = lean_nat_dec_lt(v_i_527_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v_i_527_);
return v_entries_528_;
}
else
{
lean_object* v_k_531_; lean_object* v_v_532_; uint64_t v___x_533_; size_t v_h_534_; size_t v___x_535_; lean_object* v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v_h_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_k_531_ = lean_array_fget_borrowed(v_keys_525_, v_i_527_);
v_v_532_ = lean_array_fget_borrowed(v_vals_526_, v_i_527_);
v___x_533_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_k_531_);
v_h_534_ = lean_uint64_to_usize(v___x_533_);
v___x_535_ = ((size_t)5ULL);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_sub(v_depth_524_, v___x_537_);
v___x_539_ = lean_usize_mul(v___x_535_, v___x_538_);
v_h_540_ = lean_usize_shift_right(v_h_534_, v___x_539_);
v___x_541_ = lean_nat_add(v_i_527_, v___x_536_);
lean_dec(v_i_527_);
lean_inc(v_v_532_);
lean_inc(v_k_531_);
v___x_542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_entries_528_, v_h_540_, v_depth_524_, v_k_531_, v_v_532_);
v_i_527_ = v___x_541_;
v_entries_528_ = v___x_542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg___boxed(lean_object* v_depth_544_, lean_object* v_keys_545_, lean_object* v_vals_546_, lean_object* v_i_547_, lean_object* v_entries_548_){
_start:
{
size_t v_depth_boxed_549_; lean_object* v_res_550_; 
v_depth_boxed_549_ = lean_unbox_usize(v_depth_544_);
lean_dec(v_depth_544_);
v_res_550_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_depth_boxed_549_, v_keys_545_, v_vals_546_, v_i_547_, v_entries_548_);
lean_dec_ref(v_vals_546_);
lean_dec_ref(v_keys_545_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
size_t v_x_21796__boxed_556_; size_t v_x_21797__boxed_557_; lean_object* v_res_558_; 
v_x_21796__boxed_556_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_x_21797__boxed_557_ = lean_unbox_usize(v_x_553_);
lean_dec(v_x_553_);
v_res_558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_551_, v_x_21796__boxed_556_, v_x_21797__boxed_557_, v_x_554_, v_x_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
uint64_t v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_562_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_560_);
v___x_563_ = lean_uint64_to_usize(v___x_562_);
v___x_564_ = ((size_t)1ULL);
v___x_565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_559_, v___x_563_, v___x_564_, v_x_560_, v_x_561_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(lean_object* v_keys_566_, lean_object* v_vals_567_, lean_object* v_i_568_, lean_object* v_k_569_){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_array_get_size(v_keys_566_);
v___x_571_ = lean_nat_dec_lt(v_i_568_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec(v_i_568_);
v___x_572_ = lean_box(0);
return v___x_572_;
}
else
{
lean_object* v_k_x27_573_; uint8_t v___x_574_; 
v_k_x27_573_ = lean_array_fget_borrowed(v_keys_566_, v_i_568_);
v___x_574_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_569_, v_k_x27_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_i_568_, v___x_575_);
lean_dec(v_i_568_);
v_i_568_ = v___x_576_;
goto _start;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_array_fget_borrowed(v_vals_567_, v_i_568_);
lean_dec(v_i_568_);
lean_inc(v___x_578_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg___boxed(lean_object* v_keys_580_, lean_object* v_vals_581_, lean_object* v_i_582_, lean_object* v_k_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_keys_580_, v_vals_581_, v_i_582_, v_k_583_);
lean_dec_ref(v_k_583_);
lean_dec_ref(v_vals_581_);
lean_dec_ref(v_keys_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object* v_x_585_, size_t v_x_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v_es_588_; lean_object* v___x_589_; size_t v___x_590_; size_t v___x_591_; lean_object* v_j_592_; lean_object* v___x_593_; 
v_es_588_ = lean_ctor_get(v_x_585_, 0);
v___x_589_ = lean_box(2);
v___x_590_ = ((size_t)31ULL);
v___x_591_ = lean_usize_land(v_x_586_, v___x_590_);
v_j_592_ = lean_usize_to_nat(v___x_591_);
v___x_593_ = lean_array_get_borrowed(v___x_589_, v_es_588_, v_j_592_);
lean_dec(v_j_592_);
switch(lean_obj_tag(v___x_593_))
{
case 0:
{
lean_object* v_key_594_; lean_object* v_val_595_; uint8_t v___x_596_; 
v_key_594_ = lean_ctor_get(v___x_593_, 0);
v_val_595_ = lean_ctor_get(v___x_593_, 1);
v___x_596_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_587_, v_key_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
return v___x_597_;
}
else
{
lean_object* v___x_598_; 
lean_inc(v_val_595_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_val_595_);
return v___x_598_;
}
}
case 1:
{
lean_object* v_node_599_; size_t v___x_600_; size_t v___x_601_; 
v_node_599_ = lean_ctor_get(v___x_593_, 0);
v___x_600_ = ((size_t)5ULL);
v___x_601_ = lean_usize_shift_right(v_x_586_, v___x_600_);
v_x_585_ = v_node_599_;
v_x_586_ = v___x_601_;
goto _start;
}
default: 
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(0);
return v___x_603_;
}
}
}
else
{
lean_object* v_ks_604_; lean_object* v_vs_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_ks_604_ = lean_ctor_get(v_x_585_, 0);
v_vs_605_ = lean_ctor_get(v_x_585_, 1);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_ks_604_, v_vs_605_, v___x_606_, v_x_587_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
size_t v_x_21980__boxed_611_; lean_object* v_res_612_; 
v_x_21980__boxed_611_ = lean_unbox_usize(v_x_609_);
lean_dec(v_x_609_);
v_res_612_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_608_, v_x_21980__boxed_611_, v_x_610_);
lean_dec_ref(v_x_610_);
lean_dec_ref(v_x_608_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
uint64_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_615_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_614_);
v___x_616_ = lean_uint64_to_usize(v___x_615_);
v___x_617_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_613_, v___x_616_, v_x_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_618_, v_x_619_);
lean_dec_ref(v_x_619_);
lean_dec_ref(v_x_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object* v___x_626_, lean_object* v_a_627_, lean_object* v_s_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_s_628_, v___x_626_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_s_628_, v___x_626_, v_a_627_);
return v___x_630_;
}
else
{
lean_object* v_val_631_; uint8_t v___x_632_; 
lean_dec_ref(v___x_626_);
v_val_631_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_629_, 1);
v___x_632_ = lean_name_eq(v_val_631_, v_a_627_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_633_ = 1;
v___x_634_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0));
v___x_635_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1));
v___x_636_ = lean_unsigned_to_nat(144u);
v___x_637_ = lean_unsigned_to_nat(8u);
v___x_638_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2));
v___x_639_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_627_, v___x_633_);
v___x_640_ = lean_string_append(v___x_638_, v___x_639_);
lean_dec_ref(v___x_639_);
v___x_641_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3));
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
v___x_643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_631_, v___x_633_);
v___x_644_ = lean_string_append(v___x_642_, v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4));
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
v___x_647_ = l_mkPanicMessageWithDecl(v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___x_646_);
lean_dec_ref(v___x_646_);
v___x_648_ = lean_panic_fn_borrowed(v_s_628_, v___x_647_);
lean_dec_ref(v_s_628_);
return v___x_648_;
}
else
{
lean_dec(v_val_631_);
lean_dec(v_a_627_);
return v_s_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v___x_651_, uint8_t v___x_652_, lean_object* v_h_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; 
v___x_659_ = lean_array_push(v___x_649_, v_h_653_);
v___x_660_ = l_Lean_mkAppN(v___x_650_, v___x_651_);
v___x_661_ = 1;
v___x_662_ = 1;
v___x_663_ = l_Lean_Meta_mkForallFVars(v___x_659_, v___x_660_, v___x_652_, v___x_661_, v___x_661_, v___x_662_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec_ref(v___x_659_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v_h_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v___x_22101__boxed_674_; lean_object* v_res_675_; 
v___x_22101__boxed_674_ = lean_unbox(v___x_667_);
v_res_675_ = l_Lean_Meta_mkSparseCasesOn___lam__1(v___x_664_, v___x_665_, v___x_666_, v___x_22101__boxed_674_, v_h_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___x_666_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(lean_object* v_msgData_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; lean_object* v_env_683_; uint8_t v___x_684_; lean_object* v_env_685_; lean_object* v___x_686_; lean_object* v_toCold_687_; lean_object* v_mctx_688_; lean_object* v_lctx_689_; lean_object* v_options_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_682_ = lean_st_ref_get(v___y_680_);
v_env_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref(v_env_683_);
lean_dec(v___x_682_);
v___x_684_ = 0;
v_env_685_ = l_Lean_Environment_setRecordingDeps(v_env_683_, v___x_684_);
v___x_686_ = lean_st_ref_get(v___y_678_);
v_toCold_687_ = lean_ctor_get(v___y_679_, 0);
v_mctx_688_ = lean_ctor_get(v___x_686_, 0);
lean_inc_ref(v_mctx_688_);
lean_dec(v___x_686_);
v_lctx_689_ = lean_ctor_get(v___y_677_, 2);
v_options_690_ = lean_ctor_get(v_toCold_687_, 2);
lean_inc_ref(v_options_690_);
lean_inc_ref(v_lctx_689_);
v___x_691_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_691_, 0, v_env_685_);
lean_ctor_set(v___x_691_, 1, v_mctx_688_);
lean_ctor_set(v___x_691_, 2, v_lctx_689_);
lean_ctor_set(v___x_691_, 3, v_options_690_);
v___x_692_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_msgData_676_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20___boxed(lean_object* v_msgData_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(v_msgData_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_ref_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_ref_707_ = lean_ctor_get(v___y_704_, 2);
v___x_708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_inc(v_ref_707_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_ref_707_);
lean_ctor_set(v___x_713_, 1, v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 1);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_instMonadEIO___redArg();
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_toApplicative_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_799_; 
v___x_736_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0);
v___x_737_ = l_StateRefT_x27_instMonad___redArg(v___x_736_);
v_toApplicative_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; 
v_unused_800_ = lean_ctor_get(v___x_737_, 1);
lean_dec(v_unused_800_);
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_799_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_toApplicative_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_799_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_toFunctor_742_; lean_object* v_toSeq_743_; lean_object* v_toSeqLeft_744_; lean_object* v_toSeqRight_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_797_; 
v_toFunctor_742_ = lean_ctor_get(v_toApplicative_738_, 0);
v_toSeq_743_ = lean_ctor_get(v_toApplicative_738_, 2);
v_toSeqLeft_744_ = lean_ctor_get(v_toApplicative_738_, 3);
v_toSeqRight_745_ = lean_ctor_get(v_toApplicative_738_, 4);
v_isSharedCheck_797_ = !lean_is_exclusive(v_toApplicative_738_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v_toApplicative_738_, 1);
lean_dec(v_unused_798_);
v___x_747_ = v_toApplicative_738_;
v_isShared_748_ = v_isSharedCheck_797_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_toSeqRight_745_);
lean_inc(v_toSeqLeft_744_);
lean_inc(v_toSeq_743_);
lean_inc(v_toFunctor_742_);
lean_dec(v_toApplicative_738_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_797_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___x_758_; 
v___f_749_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1));
v___f_750_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_742_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_751_, 0, v_toFunctor_742_);
v___f_752_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_752_, 0, v_toFunctor_742_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___f_751_);
lean_ctor_set(v___x_753_, 1, v___f_752_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_754_, 0, v_toSeqRight_745_);
v___f_755_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_755_, 0, v_toSeqLeft_744_);
v___f_756_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_756_, 0, v_toSeq_743_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 4, v___f_754_);
lean_ctor_set(v___x_747_, 3, v___f_755_);
lean_ctor_set(v___x_747_, 2, v___f_756_);
lean_ctor_set(v___x_747_, 1, v___f_749_);
lean_ctor_set(v___x_747_, 0, v___x_753_);
v___x_758_ = v___x_747_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___f_749_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v___f_756_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v___f_755_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v___f_754_);
v___x_758_ = v_reuseFailAlloc_796_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___f_750_);
lean_ctor_set(v___x_740_, 0, v___x_758_);
v___x_760_ = v___x_740_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___f_750_);
v___x_760_ = v_reuseFailAlloc_795_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v_toApplicative_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_793_; 
v___x_761_ = l_StateRefT_x27_instMonad___redArg(v___x_760_);
v_toApplicative_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v___x_761_, 1);
lean_dec(v_unused_794_);
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_793_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_toApplicative_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_793_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_toFunctor_766_; lean_object* v_toSeq_767_; lean_object* v_toSeqLeft_768_; lean_object* v_toSeqRight_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_791_; 
v_toFunctor_766_ = lean_ctor_get(v_toApplicative_762_, 0);
v_toSeq_767_ = lean_ctor_get(v_toApplicative_762_, 2);
v_toSeqLeft_768_ = lean_ctor_get(v_toApplicative_762_, 3);
v_toSeqRight_769_ = lean_ctor_get(v_toApplicative_762_, 4);
v_isSharedCheck_791_ = !lean_is_exclusive(v_toApplicative_762_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_toApplicative_762_, 1);
lean_dec(v_unused_792_);
v___x_771_ = v_toApplicative_762_;
v_isShared_772_ = v_isSharedCheck_791_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_toSeqRight_769_);
lean_inc(v_toSeqLeft_768_);
lean_inc(v_toSeq_767_);
lean_inc(v_toFunctor_766_);
lean_dec(v_toApplicative_762_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_791_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___x_782_; 
v___f_773_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3));
v___f_774_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_766_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_775_, 0, v_toFunctor_766_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_776_, 0, v_toFunctor_766_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___f_775_);
lean_ctor_set(v___x_777_, 1, v___f_776_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_778_, 0, v_toSeqRight_769_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_779_, 0, v_toSeqLeft_768_);
v___f_780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_780_, 0, v_toSeq_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 4, v___f_778_);
lean_ctor_set(v___x_771_, 3, v___f_779_);
lean_ctor_set(v___x_771_, 2, v___f_780_);
lean_ctor_set(v___x_771_, 1, v___f_773_);
lean_ctor_set(v___x_771_, 0, v___x_777_);
v___x_782_ = v___x_771_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___f_773_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v___f_780_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v___f_779_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v___f_778_);
v___x_782_ = v_reuseFailAlloc_790_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v___f_774_);
lean_ctor_set(v___x_764_, 0, v___x_782_);
v___x_784_ = v___x_764_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___f_774_);
v___x_784_ = v_reuseFailAlloc_789_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_17943__overap_787_; lean_object* v___x_788_; 
v___x_785_ = lean_box(0);
v___x_786_ = l_instInhabitedOfMonad___redArg(v___x_784_, v___x_785_);
v___x_17943__overap_787_ = lean_panic_fn_borrowed(v___x_786_, v_msg_730_);
lean_dec(v___x_786_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
v___x_788_ = lean_apply_5(v___x_17943__overap_787_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
return v___x_788_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v_msg_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_807_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_816_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_817_ = lean_unsigned_to_nat(11u);
v___x_818_ = lean_unsigned_to_nat(122u);
v___x_819_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4));
v___x_820_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3));
v___x_821_ = l_mkPanicMessageWithDecl(v___x_820_, v___x_819_, v___x_818_, v___x_817_, v___x_816_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object* v_constName_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_836_; lean_object* v_env_837_; uint8_t v___x_838_; lean_object* v___x_839_; 
v___x_836_ = lean_st_ref_get(v___y_826_);
v_env_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc_ref(v_env_837_);
lean_dec(v___x_836_);
v___x_838_ = 0;
lean_inc(v_constName_822_);
v___x_839_ = l_Lean_Environment_findAsync_x3f(v_env_837_, v_constName_822_, v___x_838_);
if (lean_obj_tag(v___x_839_) == 1)
{
lean_object* v_val_840_; uint8_t v_kind_841_; 
v_val_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v___x_839_, 1);
v_kind_841_ = lean_ctor_get_uint8(v_val_840_, sizeof(void*)*3);
if (v_kind_841_ == 6)
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_840_);
if (lean_obj_tag(v___x_842_) == 6)
{
lean_object* v_val_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_constName_822_);
v_val_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_val_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_val_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref(v___x_842_);
v___x_851_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6);
v___x_852_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v___x_851_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
if (lean_obj_tag(v_a_853_) == 0)
{
lean_del_object(v___x_855_);
goto v___jp_828_;
}
else
{
lean_object* v_val_857_; lean_object* v___x_859_; 
lean_dec(v_constName_822_);
v_val_857_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v_a_853_, 1);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_val_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_val_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_constName_822_);
v_a_862_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_852_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_852_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
else
{
lean_dec(v_val_840_);
goto v___jp_828_;
}
}
else
{
lean_dec(v___x_839_);
goto v___jp_828_;
}
v___jp_828_:
{
lean_object* v___x_829_; uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_829_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_830_ = 0;
v___x_831_ = l_Lean_MessageData_ofConstName(v_constName_822_, v___x_830_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_829_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_834_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object* v_constName_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_constName_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(lean_object* v_xs_877_, lean_object* v_v_878_, lean_object* v_i_879_){
_start:
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_array_get_size(v_xs_877_);
v___x_881_ = lean_nat_dec_lt(v_i_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
lean_dec(v_i_879_);
v___x_882_ = lean_box(0);
return v___x_882_;
}
else
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_array_fget_borrowed(v_xs_877_, v_i_879_);
v___x_884_ = lean_name_eq(v___x_883_, v_v_878_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_add(v_i_879_, v___x_885_);
lean_dec(v_i_879_);
v_i_879_ = v___x_886_;
goto _start;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v_i_879_);
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24___boxed(lean_object* v_xs_889_, lean_object* v_v_890_, lean_object* v_i_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(v_xs_889_, v_v_890_, v_i_891_);
lean_dec(v_v_890_);
lean_dec_ref(v_xs_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(lean_object* v_xs_893_, lean_object* v_v_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(v_xs_893_, v_v_894_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16___boxed(lean_object* v_xs_897_, lean_object* v_v_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(v_xs_897_, v_v_898_);
lean_dec(v_v_898_);
lean_dec_ref(v_xs_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object* v_xs_900_, lean_object* v_v_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(v_xs_900_, v_v_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v___x_903_; 
v___x_903_ = lean_box(0);
return v___x_903_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_val_904_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_902_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_val_904_);
lean_dec(v___x_902_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_val_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object* v_xs_912_, lean_object* v_v_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_xs_912_, v_v_913_);
lean_dec(v_v_913_);
lean_dec_ref(v_xs_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(lean_object* v_ctors_915_, lean_object* v_a_916_, lean_object* v___x_917_, lean_object* v_a_918_, uint8_t v___x_919_, uint8_t v___x_920_, lean_object* v_a_921_, lean_object* v_ys_922_, lean_object* v_x_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_ctors_915_, v_a_916_);
if (lean_obj_tag(v___x_929_) == 1)
{
lean_object* v_val_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; 
lean_dec(v_a_916_);
v_val_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v___x_929_, 1);
lean_inc_ref(v_ys_922_);
v___x_931_ = lean_array_pop(v_ys_922_);
v___x_932_ = lean_array_get_borrowed(v___x_917_, v_a_918_, v_val_930_);
lean_dec(v_val_930_);
lean_inc(v___x_932_);
v___x_933_ = l_Lean_mkAppN(v___x_932_, v___x_931_);
lean_dec_ref(v___x_931_);
v___x_934_ = 1;
v___x_935_ = l_Lean_Meta_mkLambdaFVars(v_ys_922_, v___x_933_, v___x_919_, v___x_920_, v___x_919_, v___x_920_, v___x_934_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec_ref(v_ys_922_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v___x_929_);
v___x_936_ = lean_array_get_size(v_ys_922_);
v___x_937_ = lean_unsigned_to_nat(1u);
v___x_938_ = lean_nat_sub(v___x_936_, v___x_937_);
v___x_939_ = lean_array_get_borrowed(v___x_917_, v_ys_922_, v___x_938_);
lean_dec(v___x_938_);
v___x_940_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_a_916_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_cidx_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v_cidx_942_ = lean_ctor_get(v_a_941_, 2);
lean_inc(v_cidx_942_);
lean_dec(v_a_941_);
v___x_943_ = l_Lean_mkRawNatLit(v_cidx_942_);
v___x_944_ = l_Lean_mkHasNotBitProof(v___x_943_, v_a_921_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
lean_inc(v___x_939_);
v___x_946_ = l_Lean_Expr_app___override(v___x_939_, v_a_945_);
v___x_947_ = 1;
v___x_948_ = l_Lean_Meta_mkLambdaFVars(v_ys_922_, v___x_946_, v___x_919_, v___x_920_, v___x_919_, v___x_920_, v___x_947_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec_ref(v_ys_922_);
return v___x_948_;
}
else
{
lean_dec_ref(v_ys_922_);
return v___x_944_;
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v_ys_922_);
v_a_949_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_940_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_940_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed(lean_object* v_ctors_957_, lean_object* v_a_958_, lean_object* v___x_959_, lean_object* v_a_960_, lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v_a_963_, lean_object* v_ys_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_22520__boxed_971_; uint8_t v___x_22521__boxed_972_; lean_object* v_res_973_; 
v___x_22520__boxed_971_ = lean_unbox(v___x_961_);
v___x_22521__boxed_972_ = lean_unbox(v___x_962_);
v_res_973_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(v_ctors_957_, v_a_958_, v___x_959_, v_a_960_, v___x_22520__boxed_971_, v___x_22521__boxed_972_, v_a_963_, v_ys_964_, v_x_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_x_965_);
lean_dec_ref(v_a_963_);
lean_dec_ref(v_a_960_);
lean_dec_ref(v___x_959_);
lean_dec_ref(v_ctors_957_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object* v_ctors_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_as_977_, lean_object* v_bs_978_, lean_object* v_i_979_, lean_object* v_cs_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_array_get_size(v_as_977_);
v___x_987_ = lean_nat_dec_lt(v_i_979_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v_i_979_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec_ref(v_ctors_974_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_cs_980_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_array_get_size(v_bs_978_);
v___x_990_ = lean_nat_dec_lt(v_i_979_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_dec(v_i_979_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec_ref(v_ctors_974_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_cs_980_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; uint8_t v___x_993_; lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v_b_998_; lean_object* v___x_999_; 
v___x_992_ = l_Lean_instInhabitedExpr;
v___x_993_ = 0;
v_a_994_ = lean_array_fget_borrowed(v_as_977_, v_i_979_);
v___x_995_ = lean_box(v___x_993_);
v___x_996_ = lean_box(v___x_990_);
lean_inc_ref(v_a_976_);
lean_inc_ref(v_a_975_);
lean_inc(v_a_994_);
lean_inc_ref(v_ctors_974_);
v___f_997_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed), 14, 7);
lean_closure_set(v___f_997_, 0, v_ctors_974_);
lean_closure_set(v___f_997_, 1, v_a_994_);
lean_closure_set(v___f_997_, 2, v___x_992_);
lean_closure_set(v___f_997_, 3, v_a_975_);
lean_closure_set(v___f_997_, 4, v___x_995_);
lean_closure_set(v___f_997_, 5, v___x_996_);
lean_closure_set(v___f_997_, 6, v_a_976_);
v_b_998_ = lean_array_fget_borrowed(v_bs_978_, v_i_979_);
lean_inc(v_b_998_);
v___x_999_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_b_998_, v___f_997_, v___x_993_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_i_979_, v___x_1001_);
lean_dec(v_i_979_);
v___x_1003_ = lean_array_push(v_cs_980_, v_a_1000_);
v_i_979_ = v___x_1002_;
v_cs_980_ = v___x_1003_;
goto _start;
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_cs_980_);
lean_dec(v_i_979_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec_ref(v_ctors_974_);
v_a_1005_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_999_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object* v_ctors_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_as_1016_, lean_object* v_bs_1017_, lean_object* v_i_1018_, lean_object* v_cs_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_ctors_1013_, v_a_1014_, v_a_1015_, v_as_1016_, v_bs_1017_, v_i_1018_, v_cs_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec_ref(v_bs_1017_);
lean_dec_ref(v_as_1016_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(lean_object* v_k_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
lean_inc(v___y_1031_);
lean_inc_ref(v___y_1030_);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
v___x_1033_ = lean_apply_6(v_k_1026_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, lean_box(0));
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed(lean_object* v_k_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(v_k_1034_, v_b_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(lean_object* v_name_1042_, uint8_t v_bi_1043_, lean_object* v_type_1044_, lean_object* v_k_1045_, uint8_t v_kind_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___f_1052_; lean_object* v___x_1053_; 
v___f_1052_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1052_, 0, v_k_1045_);
v___x_1053_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1042_, v_bi_1043_, v_type_1044_, v___f_1052_, v_kind_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1053_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1053_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___boxed(lean_object* v_name_1070_, lean_object* v_bi_1071_, lean_object* v_type_1072_, lean_object* v_k_1073_, lean_object* v_kind_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v_bi_boxed_1080_; uint8_t v_kind_boxed_1081_; lean_object* v_res_1082_; 
v_bi_boxed_1080_ = lean_unbox(v_bi_1071_);
v_kind_boxed_1081_ = lean_unbox(v_kind_1074_);
v_res_1082_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_1070_, v_bi_boxed_1080_, v_type_1072_, v_k_1073_, v_kind_boxed_1081_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(lean_object* v_name_1083_, lean_object* v_type_1084_, lean_object* v_k_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
uint8_t v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = 0;
v___x_1092_ = 0;
v___x_1093_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_1083_, v___x_1091_, v_type_1084_, v_k_1085_, v___x_1092_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg___boxed(lean_object* v_name_1094_, lean_object* v_type_1095_, lean_object* v_k_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v_name_1094_, v_type_1095_, v_k_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(size_t v_sz_1103_, size_t v_i_1104_, lean_object* v_bs_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_usize_dec_lt(v_i_1104_, v_sz_1103_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_bs_1105_);
return v___x_1112_;
}
else
{
lean_object* v_v_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; lean_object* v___x_1116_; 
v_v_1113_ = lean_array_uget(v_bs_1105_, v_i_1104_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1105_, v_i_1104_, v___x_1114_);
v___x_1116_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_1113_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v_cidx_1118_; size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v_cidx_1118_ = lean_ctor_get(v_a_1117_, 2);
lean_inc(v_cidx_1118_);
lean_dec(v_a_1117_);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1104_, v___x_1119_);
v___x_1121_ = lean_array_uset(v_bs_x27_1115_, v_i_1104_, v_cidx_1118_);
v_i_1104_ = v___x_1120_;
v_bs_1105_ = v___x_1121_;
goto _start;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_bs_x27_1115_);
v_a_1123_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1116_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object* v_sz_1131_, lean_object* v_i_1132_, lean_object* v_bs_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
size_t v_sz_boxed_1139_; size_t v_i_boxed_1140_; lean_object* v_res_1141_; 
v_sz_boxed_1139_ = lean_unbox_usize(v_sz_1131_);
lean_dec(v_sz_1131_);
v_i_boxed_1140_ = lean_unbox_usize(v_i_1132_);
lean_dec(v_i_1132_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_sz_boxed_1139_, v_i_boxed_1140_, v_bs_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(lean_object* v___x_1142_, size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_bs_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_usize_dec_lt(v_i_1144_, v_sz_1143_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_bs_1145_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v_v_1154_; lean_object* v___x_1155_; lean_object* v_bs_x27_1156_; lean_object* v_a_1158_; lean_object* v___x_1163_; 
v___x_1153_ = l_Lean_instInhabitedExpr;
v_v_1154_ = lean_array_uget(v_bs_1145_, v_i_1144_);
v___x_1155_ = lean_unsigned_to_nat(0u);
v_bs_x27_1156_ = lean_array_uset(v_bs_1145_, v_i_1144_, v___x_1155_);
v___x_1163_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_1154_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_cidx_1165_; lean_object* v_start_1166_; lean_object* v_stop_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v_cidx_1165_ = lean_ctor_get(v_a_1164_, 2);
lean_inc(v_cidx_1165_);
lean_dec(v_a_1164_);
v_start_1166_ = lean_ctor_get(v___x_1142_, 1);
v_stop_1167_ = lean_ctor_get(v___x_1142_, 2);
v___x_1168_ = lean_nat_sub(v_stop_1167_, v_start_1166_);
v___x_1169_ = lean_nat_dec_lt(v_cidx_1165_, v___x_1168_);
lean_dec(v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
lean_dec(v_cidx_1165_);
v___x_1170_ = l_outOfBounds___redArg(v___x_1153_);
v_a_1158_ = v___x_1170_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Subarray_get___redArg(v___x_1142_, v_cidx_1165_);
lean_dec(v_cidx_1165_);
v_a_1158_ = v___x_1171_;
goto v___jp_1157_;
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v_bs_x27_1156_);
v_a_1172_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1163_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1163_);
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
v___jp_1157_:
{
size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = ((size_t)1ULL);
v___x_1160_ = lean_usize_add(v_i_1144_, v___x_1159_);
v___x_1161_ = lean_array_uset(v_bs_x27_1156_, v_i_1144_, v_a_1158_);
v_i_1144_ = v___x_1160_;
v_bs_1145_ = v___x_1161_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object* v___x_1180_, lean_object* v_sz_1181_, lean_object* v_i_1182_, lean_object* v_bs_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
size_t v_sz_boxed_1189_; size_t v_i_boxed_1190_; lean_object* v_res_1191_; 
v_sz_boxed_1189_ = lean_unbox_usize(v_sz_1181_);
lean_dec(v_sz_1181_);
v_i_boxed_1190_ = lean_unbox_usize(v_i_1182_);
lean_dec(v_i_1182_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v___x_1180_, v_sz_boxed_1189_, v_i_boxed_1190_, v_bs_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v___x_1180_);
return v_res_1191_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5));
v___x_1202_ = l_Lean_stringToMessageData(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object* v_numParams_1203_, lean_object* v___x_1204_, lean_object* v_numIndices_1205_, uint8_t v___x_1206_, lean_object* v_ctors_1207_, lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v_a_1210_, lean_object* v_ctors_1211_, lean_object* v___x_1212_, lean_object* v_xs_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1328_ = lean_array_get_size(v_xs_1213_);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_add(v_numParams_1203_, v___x_1329_);
v___x_1331_ = lean_nat_add(v___x_1330_, v_numIndices_1205_);
lean_dec(v___x_1330_);
v___x_1332_ = lean_nat_add(v___x_1331_, v___x_1329_);
lean_dec(v___x_1331_);
v___x_1333_ = l_List_lengthTR___redArg(v_ctors_1211_);
v___x_1334_ = lean_nat_add(v___x_1332_, v___x_1333_);
lean_dec(v___x_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_nat_dec_eq(v___x_1328_, v___x_1334_);
lean_dec(v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_xs_1213_);
lean_dec(v_ctors_1211_);
lean_dec(v___x_1209_);
lean_dec(v___x_1208_);
lean_dec_ref(v_ctors_1207_);
lean_dec(v_numParams_1203_);
v___x_1336_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6, &l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once, _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6);
v___x_1337_ = l_Lean_MessageData_ofConstName(v___x_1212_, v___x_1335_);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1340_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
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
else
{
lean_dec(v___x_1212_);
v___y_1221_ = v___y_1215_;
v___y_1222_ = v___y_1216_;
v___y_1223_ = v___y_1217_;
v___y_1224_ = v___y_1218_;
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; size_t v_sz_1242_; size_t v___x_1243_; lean_object* v___x_1244_; 
v___x_1225_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1203_);
lean_inc_ref_n(v_xs_1213_, 2);
v___x_1226_ = l_Array_toSubarray___redArg(v_xs_1213_, v___x_1225_, v_numParams_1203_);
v___x_1227_ = lean_array_get(v___x_1204_, v_xs_1213_, v_numParams_1203_);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_add(v_numParams_1203_, v___x_1228_);
lean_dec(v_numParams_1203_);
v___x_1230_ = lean_nat_add(v___x_1229_, v_numIndices_1205_);
lean_inc(v___x_1230_);
v___x_1231_ = l_Array_toSubarray___redArg(v_xs_1213_, v___x_1229_, v___x_1230_);
v___x_1232_ = lean_array_get(v___x_1204_, v_xs_1213_, v___x_1230_);
v___x_1233_ = l_Subarray_copy___redArg(v___x_1231_);
v___x_1234_ = lean_mk_empty_array_with_capacity(v___x_1228_);
lean_inc(v___x_1232_);
lean_inc_ref_n(v___x_1234_, 2);
v___x_1235_ = lean_array_push(v___x_1234_, v___x_1232_);
lean_inc_ref(v___x_1233_);
v___x_1236_ = l_Array_append___redArg(v___x_1233_, v___x_1235_);
v___x_1237_ = lean_box(v___x_1206_);
lean_inc_ref(v___x_1236_);
lean_inc(v___x_1227_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1238_, 0, v___x_1234_);
lean_closure_set(v___f_1238_, 1, v___x_1227_);
lean_closure_set(v___f_1238_, 2, v___x_1236_);
lean_closure_set(v___f_1238_, 3, v___x_1237_);
v___x_1239_ = lean_nat_add(v___x_1230_, v___x_1228_);
lean_dec(v___x_1230_);
v___x_1240_ = lean_array_get_size(v_xs_1213_);
v___x_1241_ = l_Array_toSubarray___redArg(v_xs_1213_, v___x_1239_, v___x_1240_);
v_sz_1242_ = lean_array_size(v_ctors_1207_);
v___x_1243_ = ((size_t)0ULL);
lean_inc_ref(v_ctors_1207_);
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v___x_1241_, v_sz_1242_, v___x_1243_, v_ctors_1207_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec_ref(v___x_1241_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
lean_inc_ref(v_ctors_1207_);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_sz_1242_, v___x_1243_, v_ctors_1207_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = l_Lean_mkConst(v___x_1208_, v___x_1209_);
v___x_1249_ = l_Subarray_copy___redArg(v___x_1226_);
lean_inc_ref(v___x_1249_);
v___x_1250_ = l_Array_append___redArg(v___x_1249_, v___x_1233_);
v___x_1251_ = l_Array_append___redArg(v___x_1250_, v___x_1235_);
v___x_1252_ = l_Lean_mkAppN(v___x_1248_, v___x_1251_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = l_Lean_mkHasNotBit(v___x_1252_, v_a_1247_);
v___x_1254_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1));
v___x_1255_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v___x_1254_, v___x_1253_, v___f_1238_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = l_Lean_ConstantInfo_value_x21(v_a_1210_, v___x_1206_);
v___x_1258_ = l_Lean_mkAppN(v___x_1257_, v___x_1249_);
v___x_1259_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3));
v___x_1260_ = l_Lean_Core_mkFreshUserName(v___x_1259_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = 0;
lean_inc(v___x_1227_);
v___x_1263_ = l_Lean_mkAppN(v___x_1227_, v___x_1236_);
v___x_1264_ = l_Lean_mkForall(v_a_1261_, v___x_1262_, v_a_1256_, v___x_1263_);
v___x_1265_ = 1;
v___x_1266_ = 1;
v___x_1267_ = l_Lean_Meta_mkLambdaFVars(v___x_1236_, v___x_1264_, v___x_1206_, v___x_1265_, v___x_1206_, v___x_1265_, v___x_1266_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec_ref(v___x_1236_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = l_Lean_Expr_app___override(v___x_1258_, v_a_1268_);
v___x_1270_ = l_Lean_mkAppN(v___x_1269_, v___x_1233_);
v___x_1271_ = l_Lean_Expr_app___override(v___x_1270_, v___x_1232_);
v___x_1272_ = l_List_lengthTR___redArg(v_ctors_1211_);
lean_inc_ref(v___x_1271_);
v___x_1273_ = l_Lean_Meta_inferArgumentTypesN(v___x_1272_, v___x_1271_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = lean_array_mk(v_ctors_1211_);
v___x_1276_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4));
lean_inc(v_a_1245_);
v___x_1277_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_ctors_1207_, v_a_1245_, v_a_1247_, v___x_1275_, v_a_1274_, v___x_1225_, v___x_1276_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v_a_1274_);
lean_dec_ref(v___x_1275_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = l_Lean_mkAppN(v___x_1271_, v_a_1278_);
lean_dec(v_a_1278_);
v___x_1280_ = l_Lean_Core_betaReduce(v___x_1279_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_array_push(v___x_1234_, v___x_1227_);
v___x_1283_ = l_Array_append___redArg(v___x_1249_, v___x_1282_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = l_Array_append___redArg(v___x_1283_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1285_ = l_Array_append___redArg(v___x_1284_, v___x_1235_);
lean_dec_ref(v___x_1235_);
v___x_1286_ = l_Array_append___redArg(v___x_1285_, v_a_1245_);
lean_dec(v_a_1245_);
v___x_1287_ = l_Lean_Meta_mkLambdaFVars(v___x_1286_, v_a_1281_, v___x_1206_, v___x_1265_, v___x_1206_, v___x_1265_, v___x_1266_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec_ref(v___x_1286_);
return v___x_1287_;
}
else
{
lean_dec_ref(v___x_1249_);
lean_dec(v_a_1245_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1227_);
return v___x_1280_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1249_);
lean_dec(v_a_1245_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1227_);
v_a_1288_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1277_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1277_);
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
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v___x_1271_);
lean_dec_ref(v___x_1249_);
lean_dec(v_a_1247_);
lean_dec(v_a_1245_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1227_);
lean_dec(v_ctors_1211_);
lean_dec_ref(v_ctors_1207_);
v_a_1296_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1273_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1273_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1249_);
lean_dec(v_a_1247_);
lean_dec(v_a_1245_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1232_);
lean_dec(v___x_1227_);
lean_dec(v_ctors_1211_);
lean_dec_ref(v_ctors_1207_);
return v___x_1267_;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___x_1258_);
lean_dec(v_a_1256_);
lean_dec_ref(v___x_1249_);
lean_dec(v_a_1247_);
lean_dec(v_a_1245_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1232_);
lean_dec(v___x_1227_);
lean_dec(v_ctors_1211_);
lean_dec_ref(v_ctors_1207_);
v_a_1304_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1260_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1260_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_dec_ref(v___x_1249_);
lean_dec(v_a_1247_);
lean_dec(v_a_1245_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1232_);
lean_dec(v___x_1227_);
lean_dec(v_ctors_1211_);
lean_dec_ref(v_ctors_1207_);
return v___x_1255_;
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_a_1245_);
lean_dec_ref(v___f_1238_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1232_);
lean_dec(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec(v_ctors_1211_);
lean_dec(v___x_1209_);
lean_dec(v___x_1208_);
lean_dec_ref(v_ctors_1207_);
v_a_1312_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1246_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1246_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v___f_1238_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec(v___x_1232_);
lean_dec(v___x_1227_);
lean_dec_ref(v___x_1226_);
lean_dec(v_ctors_1211_);
lean_dec(v___x_1209_);
lean_dec(v___x_1208_);
lean_dec_ref(v_ctors_1207_);
v_a_1320_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1244_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1244_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1350_ = _args[0];
lean_object* v___x_1351_ = _args[1];
lean_object* v_numIndices_1352_ = _args[2];
lean_object* v___x_1353_ = _args[3];
lean_object* v_ctors_1354_ = _args[4];
lean_object* v___x_1355_ = _args[5];
lean_object* v___x_1356_ = _args[6];
lean_object* v_a_1357_ = _args[7];
lean_object* v_ctors_1358_ = _args[8];
lean_object* v___x_1359_ = _args[9];
lean_object* v_xs_1360_ = _args[10];
lean_object* v_x_1361_ = _args[11];
lean_object* v___y_1362_ = _args[12];
lean_object* v___y_1363_ = _args[13];
lean_object* v___y_1364_ = _args[14];
lean_object* v___y_1365_ = _args[15];
lean_object* v___y_1366_ = _args[16];
_start:
{
uint8_t v___x_22907__boxed_1367_; lean_object* v_res_1368_; 
v___x_22907__boxed_1367_ = lean_unbox(v___x_1353_);
v_res_1368_ = l_Lean_Meta_mkSparseCasesOn___lam__2(v_numParams_1350_, v___x_1351_, v_numIndices_1352_, v___x_22907__boxed_1367_, v_ctors_1354_, v___x_1355_, v___x_1356_, v_a_1357_, v_ctors_1358_, v___x_1359_, v_xs_1360_, v_x_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec_ref(v_x_1361_);
lean_dec_ref(v_a_1357_);
lean_dec(v_numIndices_1352_);
lean_dec_ref(v___x_1351_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(lean_object* v_ref_1369_, lean_object* v_msg_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_toCold_1376_; lean_object* v_currRecDepth_1377_; lean_object* v_ref_1378_; uint16_t v_optionFlags_1379_; uint8_t v_suppressElabErrors_1380_; uint8_t v_isRecordingDeps_1381_; lean_object* v_ref_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_toCold_1376_ = lean_ctor_get(v___y_1373_, 0);
v_currRecDepth_1377_ = lean_ctor_get(v___y_1373_, 1);
v_ref_1378_ = lean_ctor_get(v___y_1373_, 2);
v_optionFlags_1379_ = lean_ctor_get_uint16(v___y_1373_, sizeof(void*)*3);
v_suppressElabErrors_1380_ = lean_ctor_get_uint8(v___y_1373_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1381_ = lean_ctor_get_uint8(v___y_1373_, sizeof(void*)*3 + 3);
v_ref_1382_ = l_Lean_replaceRef(v_ref_1369_, v_ref_1378_);
lean_inc(v_currRecDepth_1377_);
lean_inc_ref(v_toCold_1376_);
v___x_1383_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1383_, 0, v_toCold_1376_);
lean_ctor_set(v___x_1383_, 1, v_currRecDepth_1377_);
lean_ctor_set(v___x_1383_, 2, v_ref_1382_);
lean_ctor_set_uint16(v___x_1383_, sizeof(void*)*3, v_optionFlags_1379_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 2, v_suppressElabErrors_1380_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 3, v_isRecordingDeps_1381_);
v___x_1384_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_1370_, v___y_1371_, v___y_1372_, v___x_1383_, v___y_1374_);
lean_dec_ref_known(v___x_1383_, 3);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg___boxed(lean_object* v_ref_1385_, lean_object* v_msg_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_1385_, v_msg_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v_ref_1385_);
return v_res_1392_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1395_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1396_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
lean_ctor_set(v___x_1398_, 2, v___x_1397_);
lean_ctor_set(v___x_1398_, 3, v___x_1397_);
lean_ctor_set(v___x_1398_, 4, v___x_1396_);
lean_ctor_set(v___x_1398_, 5, v___x_1396_);
lean_ctor_set(v___x_1398_, 6, v___x_1396_);
lean_ctor_set(v___x_1398_, 7, v___x_1396_);
lean_ctor_set(v___x_1398_, 8, v___x_1396_);
lean_ctor_set(v___x_1398_, 9, v___x_1396_);
lean_ctor_set(v___x_1398_, 10, v___x_1396_);
lean_ctor_set(v___x_1398_, 11, v___x_1395_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_unsigned_to_nat(32u);
v___x_1400_ = lean_mk_empty_array_with_capacity(v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3(void){
_start:
{
size_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1402_ = ((size_t)5ULL);
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_unsigned_to_nat(32u);
v___x_1405_ = lean_mk_empty_array_with_capacity(v___x_1404_);
v___x_1406_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2);
v___x_1407_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___x_1405_);
lean_ctor_set(v___x_1407_, 2, v___x_1403_);
lean_ctor_set(v___x_1407_, 3, v___x_1403_);
lean_ctor_set_usize(v___x_1407_, 4, v___x_1402_);
return v___x_1407_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_box(1);
v___x_1409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3);
v___x_1410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0);
v___x_1411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1409_);
lean_ctor_set(v___x_1411_, 2, v___x_1408_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7));
v___x_1417_ = l_Lean_stringToMessageData(v___x_1416_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9));
v___x_1420_ = l_Lean_stringToMessageData(v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11));
v___x_1423_ = l_Lean_stringToMessageData(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13));
v___x_1426_ = l_Lean_stringToMessageData(v___x_1425_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(lean_object* v_msg_1433_, lean_object* v_declHint_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_env_1439_; uint8_t v___x_1440_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_st_ref_get(v___y_1435_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = l_Lean_Name_isAnonymous(v_declHint_1434_);
if (v___x_1440_ == 0)
{
uint8_t v_isExporting_1441_; 
v_isExporting_1441_ = lean_ctor_get_uint8(v_env_1439_, sizeof(void*)*13);
if (v_isExporting_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_msg_1433_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
lean_inc_ref(v_env_1439_);
v___x_1443_ = l_Lean_Environment_setExporting(v_env_1439_, v___x_1440_);
lean_inc(v_declHint_1434_);
lean_inc_ref(v___x_1443_);
v___x_1444_ = l_Lean_Environment_contains(v___x_1443_, v_declHint_1434_, v_isExporting_1441_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref(v___x_1443_);
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_msg_1433_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_c_1451_; lean_object* v___x_1452_; 
v___x_1446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1);
v___x_1447_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4);
v___x_1448_ = l_Lean_Options_empty;
v___x_1449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1443_);
lean_ctor_set(v___x_1449_, 1, v___x_1446_);
lean_ctor_set(v___x_1449_, 2, v___x_1447_);
lean_ctor_set(v___x_1449_, 3, v___x_1448_);
lean_inc(v_declHint_1434_);
v___x_1450_ = l_Lean_MessageData_ofConstName(v_declHint_1434_, v___x_1440_);
v_c_1451_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1451_, 0, v___x_1449_);
lean_ctor_set(v_c_1451_, 1, v___x_1450_);
v___x_1452_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1439_, v_declHint_1434_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6);
v___x_1454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v_c_1451_);
v___x_1455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = l_Lean_MessageData_note(v___x_1456_);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_msg_1433_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
else
{
lean_object* v_val_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1494_; 
v_val_1460_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1462_ = v___x_1452_;
v_isShared_1463_ = v_isSharedCheck_1494_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_val_1460_);
lean_dec(v___x_1452_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1494_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_mod_1466_; uint8_t v___x_1467_; 
v___x_1464_ = l_Lean_Environment_header(v_env_1439_);
lean_dec_ref(v_env_1439_);
v___x_1465_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1464_);
v_mod_1466_ = lean_array_get(v___x_1437_, v___x_1465_, v_val_1460_);
lean_dec(v_val_1460_);
lean_dec_ref(v___x_1465_);
v___x_1467_ = l_Lean_isPrivateName(v_declHint_1434_);
lean_dec(v_declHint_1434_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1468_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_c_1451_);
v___x_1470_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_MessageData_ofName(v_mod_1466_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = l_Lean_MessageData_note(v___x_1475_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_msg_1433_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1477_);
v___x_1479_ = v___x_1462_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_c_1451_);
v___x_1483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_MessageData_ofName(v_mod_1466_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_MessageData_note(v___x_1488_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_msg_1433_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1490_);
v___x_1492_ = v___x_1462_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1495_; 
lean_dec_ref(v_env_1439_);
lean_dec(v_declHint_1434_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_msg_1433_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___boxed(lean_object* v_msg_1496_, lean_object* v_declHint_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_1496_, v_declHint_1497_, v___y_1498_);
lean_dec(v___y_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(lean_object* v_msg_1501_, lean_object* v_declHint_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1518_; 
v___x_1508_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_1501_, v_declHint_1502_, v___y_1506_);
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1518_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1513_ = l_Lean_unknownIdentifierMessageTag;
v___x_1514_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_a_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1514_);
v___x_1516_ = v___x_1511_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33___boxed(lean_object* v_msg_1519_, lean_object* v_declHint_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(v_msg_1519_, v_declHint_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(lean_object* v_ref_1527_, lean_object* v_msg_1528_, lean_object* v_declHint_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_a_1536_; lean_object* v___x_1537_; 
v___x_1535_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(v_msg_1528_, v_declHint_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_1527_, v_a_1536_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg___boxed(lean_object* v_ref_1538_, lean_object* v_msg_1539_, lean_object* v_declHint_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_1538_, v_msg_1539_, v_declHint_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_ref_1538_);
return v_res_1546_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(lean_object* v_ref_1550_, lean_object* v_constName_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1557_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1);
v___x_1558_ = 0;
lean_inc(v_constName_1551_);
v___x_1559_ = l_Lean_MessageData_ofConstName(v_constName_1551_, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1557_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_1550_, v___x_1562_, v_constName_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___boxed(lean_object* v_ref_1564_, lean_object* v_constName_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_1564_, v_constName_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v_ref_1564_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(lean_object* v_constName_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_ref_1578_; lean_object* v___x_1579_; 
v_ref_1578_ = lean_ctor_get(v___y_1575_, 2);
v___x_1579_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_1578_, v_constName_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg___boxed(lean_object* v_constName_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object* v_constName_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v_env_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_st_ref_get(v___y_1591_);
v_env_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc_ref(v_env_1594_);
lean_dec(v___x_1593_);
v___x_1595_ = 0;
lean_inc(v_constName_1587_);
v___x_1596_ = l_Lean_Environment_find_x3f(v_env_1594_, v_constName_1587_, v___x_1595_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1597_;
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_constName_1587_);
v_val_1598_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1596_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v___x_1596_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_val_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6___boxed(lean_object* v_constName_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_constName_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1612_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0);
v___x_1618_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
lean_ctor_set(v___x_1618_, 2, v___x_1617_);
lean_ctor_set(v___x_1618_, 3, v___x_1617_);
lean_ctor_set(v___x_1618_, 4, v___x_1617_);
lean_ctor_set(v___x_1618_, 5, v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(lean_object* v_declName_1619_, uint8_t v_s_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; lean_object* v_env_1625_; lean_object* v_nextMacroScope_1626_; lean_object* v_ngen_1627_; lean_object* v_auxDeclNGen_1628_; lean_object* v_traceState_1629_; lean_object* v_recordedDeps_1630_; lean_object* v_messages_1631_; lean_object* v_infoState_1632_; lean_object* v_snapshotTasks_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1662_; 
v___x_1624_ = lean_st_ref_take(v___y_1622_);
v_env_1625_ = lean_ctor_get(v___x_1624_, 0);
v_nextMacroScope_1626_ = lean_ctor_get(v___x_1624_, 1);
v_ngen_1627_ = lean_ctor_get(v___x_1624_, 2);
v_auxDeclNGen_1628_ = lean_ctor_get(v___x_1624_, 3);
v_traceState_1629_ = lean_ctor_get(v___x_1624_, 4);
v_recordedDeps_1630_ = lean_ctor_get(v___x_1624_, 6);
v_messages_1631_ = lean_ctor_get(v___x_1624_, 7);
v_infoState_1632_ = lean_ctor_get(v___x_1624_, 8);
v_snapshotTasks_1633_ = lean_ctor_get(v___x_1624_, 9);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1624_, 5);
lean_dec(v_unused_1663_);
v___x_1635_ = v___x_1624_;
v_isShared_1636_ = v_isSharedCheck_1662_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_snapshotTasks_1633_);
lean_inc(v_infoState_1632_);
lean_inc(v_messages_1631_);
lean_inc(v_recordedDeps_1630_);
lean_inc(v_traceState_1629_);
lean_inc(v_auxDeclNGen_1628_);
lean_inc(v_ngen_1627_);
lean_inc(v_nextMacroScope_1626_);
lean_inc(v_env_1625_);
lean_dec(v___x_1624_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1662_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1637_ = 0;
v___x_1638_ = lean_box(0);
v___x_1639_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1625_, v_declName_1619_, v_s_1620_, v___x_1637_, v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 5, v___x_1640_);
lean_ctor_set(v___x_1635_, 0, v___x_1639_);
v___x_1642_ = v___x_1635_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_nextMacroScope_1626_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_ngen_1627_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_auxDeclNGen_1628_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_traceState_1629_);
lean_ctor_set(v_reuseFailAlloc_1661_, 5, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1661_, 6, v_recordedDeps_1630_);
lean_ctor_set(v_reuseFailAlloc_1661_, 7, v_messages_1631_);
lean_ctor_set(v_reuseFailAlloc_1661_, 8, v_infoState_1632_);
lean_ctor_set(v_reuseFailAlloc_1661_, 9, v_snapshotTasks_1633_);
v___x_1642_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_mctx_1645_; lean_object* v_zetaDeltaFVarIds_1646_; lean_object* v_postponed_1647_; lean_object* v_diag_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1659_; 
v___x_1643_ = lean_st_ref_put(v___y_1622_, v___x_1642_);
v___x_1644_ = lean_st_ref_take(v___y_1621_);
v_mctx_1645_ = lean_ctor_get(v___x_1644_, 0);
v_zetaDeltaFVarIds_1646_ = lean_ctor_get(v___x_1644_, 2);
v_postponed_1647_ = lean_ctor_get(v___x_1644_, 3);
v_diag_1648_ = lean_ctor_get(v___x_1644_, 4);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v___x_1644_, 1);
lean_dec(v_unused_1660_);
v___x_1650_ = v___x_1644_;
v_isShared_1651_ = v_isSharedCheck_1659_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_diag_1648_);
lean_inc(v_postponed_1647_);
lean_inc(v_zetaDeltaFVarIds_1646_);
lean_inc(v_mctx_1645_);
lean_dec(v___x_1644_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1659_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_mctx_1645_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_zetaDeltaFVarIds_1646_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_postponed_1647_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v_diag_1648_);
v___x_1655_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_st_ref_put(v___y_1621_, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1652_);
return v___x_1657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___boxed(lean_object* v_declName_1664_, lean_object* v_s_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v_s_boxed_1669_; lean_object* v_res_1670_; 
v_s_boxed_1669_ = lean_unbox(v_s_1665_);
v_res_1670_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_1664_, v_s_boxed_1669_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec(v___y_1666_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object* v_declName_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = 0;
v___x_1678_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_1671_, v___x_1677_, v___y_1673_, v___y_1675_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object* v_declName_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(v_declName_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object* v_a_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
uint8_t v___x_1688_; 
v___x_1688_ = 0;
return v___x_1688_;
}
else
{
lean_object* v_head_1689_; lean_object* v_tail_1690_; uint8_t v___x_1691_; 
v_head_1689_ = lean_ctor_get(v_x_1687_, 0);
v_tail_1690_ = lean_ctor_get(v_x_1687_, 1);
v___x_1691_ = lean_name_eq(v_a_1686_, v_head_1689_);
if (v___x_1691_ == 0)
{
v_x_1687_ = v_tail_1690_;
goto _start;
}
else
{
return v___x_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object* v_a_1693_, lean_object* v_x_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1693_, v_x_1694_);
lean_dec(v_x_1694_);
lean_dec(v_a_1693_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(lean_object* v_a_1703_, lean_object* v_indName_1704_, lean_object* v_as_1705_, size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_a_1715_; uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_indName_1704_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_b_1708_);
return v___x_1720_;
}
else
{
lean_object* v_ctors_1721_; lean_object* v___x_1722_; lean_object* v_a_1723_; uint8_t v___x_1724_; 
v_ctors_1721_ = lean_ctor_get(v_a_1703_, 4);
v___x_1722_ = lean_box(0);
v_a_1723_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
v___x_1724_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1723_, v_ctors_1721_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1);
lean_inc(v_a_1723_);
v___x_1726_ = l_Lean_MessageData_ofName(v_a_1723_);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
lean_inc(v_indName_1704_);
v___x_1730_ = l_Lean_MessageData_ofName(v_indName_1704_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1731_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_dec_ref_known(v___x_1732_, 1);
v_a_1715_ = v___x_1722_;
goto v___jp_1714_;
}
else
{
lean_dec(v_indName_1704_);
return v___x_1732_;
}
}
else
{
v_a_1715_ = v___x_1722_;
goto v___jp_1714_;
}
}
v___jp_1714_:
{
size_t v___x_1716_; size_t v___x_1717_; 
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_add(v_i_1707_, v___x_1716_);
v_i_1707_ = v___x_1717_;
v_b_1708_ = v_a_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___boxed(lean_object* v_a_1733_, lean_object* v_indName_1734_, lean_object* v_as_1735_, lean_object* v_sz_1736_, lean_object* v_i_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
size_t v_sz_boxed_1744_; size_t v_i_boxed_1745_; lean_object* v_res_1746_; 
v_sz_boxed_1744_ = lean_unbox_usize(v_sz_1736_);
lean_dec(v_sz_1736_);
v_i_boxed_1745_ = lean_unbox_usize(v_i_1737_);
lean_dec(v_i_1737_);
v_res_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(v_a_1733_, v_indName_1734_, v_as_1735_, v_sz_boxed_1744_, v_i_boxed_1745_, v_b_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v_as_1735_);
lean_dec_ref(v_a_1733_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
if (lean_obj_tag(v_a_1747_) == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = l_List_reverse___redArg(v_a_1748_);
return v___x_1749_;
}
else
{
lean_object* v_head_1750_; lean_object* v_tail_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1760_; 
v_head_1750_ = lean_ctor_get(v_a_1747_, 0);
v_tail_1751_ = lean_ctor_get(v_a_1747_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_a_1747_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1753_ = v_a_1747_;
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_tail_1751_);
lean_inc(v_head_1750_);
lean_dec(v_a_1747_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = l_Lean_mkLevelParam(v_head_1750_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v_a_1748_);
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_a_1748_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
v_a_1747_ = v_tail_1751_;
v_a_1748_ = v___x_1757_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0));
v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object* v_constName_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; lean_object* v_env_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_st_ref_get(v___y_1768_);
v_env_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc_ref(v_env_1771_);
lean_dec(v___x_1770_);
lean_inc(v_constName_1764_);
v___x_1772_ = l_Lean_isInductiveCore_x3f(v_env_1771_, v_constName_1764_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1773_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1774_ = 0;
v___x_1775_ = l_Lean_MessageData_ofConstName(v_constName_1764_, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1778_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1779_;
}
else
{
lean_object* v_val_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_constName_1764_);
v_val_1780_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1772_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_val_1780_);
lean_dec(v___x_1772_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 0);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_val_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object* v_constName_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
return v_res_1794_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__0(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_1796_ = lean_unsigned_to_nat(42u);
v___x_1797_ = lean_unsigned_to_nat(82u);
v___x_1798_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1));
v___x_1799_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0));
v___x_1800_ = l_mkPanicMessageWithDecl(v___x_1799_, v___x_1798_, v___x_1797_, v___x_1796_, v___x_1795_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__2(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__1));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__3(void){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__7(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__6));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object* v_indName_1811_, lean_object* v_ctors_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; uint8_t v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_2022_; uint8_t v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; uint8_t v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_env_2073_; uint8_t v___y_2075_; lean_object* v___x_2131_; uint8_t v_isModule_2132_; 
v___x_1818_ = l_Lean_instInhabitedExpr;
v___x_2071_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__3, &l_Lean_Meta_mkSparseCasesOn___closed__3_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__3);
v___x_2072_ = lean_st_ref_get(v_a_1816_);
v_env_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc_ref(v_env_2073_);
lean_dec(v___x_2072_);
v___x_2131_ = l_Lean_Environment_header(v_env_2073_);
v_isModule_2132_ = lean_ctor_get_uint8(v___x_2131_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2131_);
if (v_isModule_2132_ == 0)
{
v___y_2075_ = v_isModule_2132_;
goto v___jp_2074_;
}
else
{
uint8_t v_isExporting_2133_; 
v_isExporting_2133_ = lean_ctor_get_uint8(v_env_2073_, sizeof(void*)*13);
if (v_isExporting_2133_ == 0)
{
v___y_2075_ = v_isModule_2132_;
goto v___jp_2074_;
}
else
{
uint8_t v___x_2134_; 
v___x_2134_ = 0;
v___y_2075_ = v___x_2134_;
goto v___jp_2074_;
}
}
v___jp_1819_:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_ConstantInfo_levelParams(v___y_1828_);
if (lean_obj_tag(v___x_1839_) == 1)
{
lean_object* v_tail_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___f_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_tail_1840_ = lean_ctor_get(v___x_1839_, 1);
v___x_1841_ = lean_box(0);
lean_inc(v_tail_1840_);
v___x_1842_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(v_tail_1840_, v___x_1841_);
v___x_1843_ = lean_box(v___y_1824_);
lean_inc_ref(v_ctors_1812_);
v___f_1844_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__2___boxed), 17, 10);
lean_closure_set(v___f_1844_, 0, v___y_1826_);
lean_closure_set(v___f_1844_, 1, v___x_1818_);
lean_closure_set(v___f_1844_, 2, v___y_1823_);
lean_closure_set(v___f_1844_, 3, v___x_1843_);
lean_closure_set(v___f_1844_, 4, v_ctors_1812_);
lean_closure_set(v___f_1844_, 5, v___y_1822_);
lean_closure_set(v___f_1844_, 6, v___x_1842_);
lean_closure_set(v___f_1844_, 7, v___y_1820_);
lean_closure_set(v___f_1844_, 8, v___y_1825_);
lean_closure_set(v___f_1844_, 9, v___y_1821_);
v___x_1845_ = l_Lean_ConstantInfo_type(v___y_1828_);
lean_dec_ref(v___y_1828_);
v___x_1846_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v___x_1845_, v___f_1844_, v___y_1833_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc_n(v_a_1847_, 2);
lean_dec_ref_known(v___x_1846_, 1);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
v___x_1848_ = lean_infer_type(v_a_1847_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_2002_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = lean_box(1);
lean_inc(v___y_1830_);
v___x_1851_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v___y_1830_, v___x_1839_, v_a_1849_, v_a_1847_, v___x_1850_, v___y_1838_);
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_2002_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_2002_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set_tag(v___x_1854_, 1);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_addDecl(v___x_1857_, v___y_1833_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v___x_1859_; lean_object* v_env_1860_; lean_object* v_nextMacroScope_1861_; lean_object* v_ngen_1862_; lean_object* v_auxDeclNGen_1863_; lean_object* v_traceState_1864_; lean_object* v_recordedDeps_1865_; lean_object* v_messages_1866_; lean_object* v_infoState_1867_; lean_object* v_snapshotTasks_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref_known(v___x_1858_, 1);
v___x_1859_ = lean_st_ref_take(v___y_1838_);
v_env_1860_ = lean_ctor_get(v___x_1859_, 0);
v_nextMacroScope_1861_ = lean_ctor_get(v___x_1859_, 1);
v_ngen_1862_ = lean_ctor_get(v___x_1859_, 2);
v_auxDeclNGen_1863_ = lean_ctor_get(v___x_1859_, 3);
v_traceState_1864_ = lean_ctor_get(v___x_1859_, 4);
v_recordedDeps_1865_ = lean_ctor_get(v___x_1859_, 6);
v_messages_1866_ = lean_ctor_get(v___x_1859_, 7);
v_infoState_1867_ = lean_ctor_get(v___x_1859_, 8);
v_snapshotTasks_1868_ = lean_ctor_get(v___x_1859_, 9);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v___x_1859_, 5);
lean_dec(v_unused_1992_);
v___x_1870_ = v___x_1859_;
v_isShared_1871_ = v_isSharedCheck_1991_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snapshotTasks_1868_);
lean_inc(v_infoState_1867_);
lean_inc(v_messages_1866_);
lean_inc(v_recordedDeps_1865_);
lean_inc(v_traceState_1864_);
lean_inc(v_auxDeclNGen_1863_);
lean_inc(v_ngen_1862_);
lean_inc(v_nextMacroScope_1861_);
lean_inc(v_env_1860_);
lean_dec(v___x_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1991_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1872_ = 1;
lean_inc_ref(v___y_1829_);
v___x_1873_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___y_1829_, v_env_1860_, v___y_1834_, v___y_1827_, v___y_1831_, v___x_1872_);
v___x_1874_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 5, v___x_1874_);
lean_ctor_set(v___x_1870_, 0, v___x_1873_);
v___x_1876_ = v___x_1870_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_nextMacroScope_1861_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_ngen_1862_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_auxDeclNGen_1863_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v_traceState_1864_);
lean_ctor_set(v_reuseFailAlloc_1990_, 5, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1990_, 6, v_recordedDeps_1865_);
lean_ctor_set(v_reuseFailAlloc_1990_, 7, v_messages_1866_);
lean_ctor_set(v_reuseFailAlloc_1990_, 8, v_infoState_1867_);
lean_ctor_set(v_reuseFailAlloc_1990_, 9, v_snapshotTasks_1868_);
v___x_1876_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_mctx_1879_; lean_object* v_zetaDeltaFVarIds_1880_; lean_object* v_postponed_1881_; lean_object* v_diag_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1988_; 
v___x_1877_ = lean_st_ref_put(v___y_1838_, v___x_1876_);
v___x_1878_ = lean_st_ref_take(v___y_1836_);
v_mctx_1879_ = lean_ctor_get(v___x_1878_, 0);
v_zetaDeltaFVarIds_1880_ = lean_ctor_get(v___x_1878_, 2);
v_postponed_1881_ = lean_ctor_get(v___x_1878_, 3);
v_diag_1882_ = lean_ctor_get(v___x_1878_, 4);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v___x_1878_, 1);
lean_dec(v_unused_1989_);
v___x_1884_ = v___x_1878_;
v_isShared_1885_ = v_isSharedCheck_1988_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_diag_1882_);
lean_inc(v_postponed_1881_);
lean_inc(v_zetaDeltaFVarIds_1880_);
lean_inc(v_mctx_1879_);
lean_dec(v___x_1878_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1988_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_mctx_1879_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_zetaDeltaFVarIds_1880_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_postponed_1881_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_diag_1882_);
v___x_1888_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_env_1892_; lean_object* v_nextMacroScope_1893_; lean_object* v_ngen_1894_; lean_object* v_auxDeclNGen_1895_; lean_object* v_traceState_1896_; lean_object* v_recordedDeps_1897_; lean_object* v_messages_1898_; lean_object* v_infoState_1899_; lean_object* v_snapshotTasks_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1985_; 
v___x_1889_ = lean_st_ref_put(v___y_1836_, v___x_1888_);
lean_inc(v___y_1830_);
v___x_1890_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(v___y_1830_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec_ref(v___x_1890_);
v___x_1891_ = lean_st_ref_take(v___y_1838_);
v_env_1892_ = lean_ctor_get(v___x_1891_, 0);
v_nextMacroScope_1893_ = lean_ctor_get(v___x_1891_, 1);
v_ngen_1894_ = lean_ctor_get(v___x_1891_, 2);
v_auxDeclNGen_1895_ = lean_ctor_get(v___x_1891_, 3);
v_traceState_1896_ = lean_ctor_get(v___x_1891_, 4);
v_recordedDeps_1897_ = lean_ctor_get(v___x_1891_, 6);
v_messages_1898_ = lean_ctor_get(v___x_1891_, 7);
v_infoState_1899_ = lean_ctor_get(v___x_1891_, 8);
v_snapshotTasks_1900_ = lean_ctor_get(v___x_1891_, 9);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v___x_1891_, 5);
lean_dec(v_unused_1986_);
v___x_1902_ = v___x_1891_;
v_isShared_1903_ = v_isSharedCheck_1985_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snapshotTasks_1900_);
lean_inc(v_infoState_1899_);
lean_inc(v_messages_1898_);
lean_inc(v_recordedDeps_1897_);
lean_inc(v_traceState_1896_);
lean_inc(v_auxDeclNGen_1895_);
lean_inc(v_ngen_1894_);
lean_inc(v_nextMacroScope_1893_);
lean_inc(v_env_1892_);
lean_dec(v___x_1891_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1985_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_inc(v___y_1830_);
v___x_1904_ = l_Lean_markSparseCasesOn(v_env_1892_, v___y_1830_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 5, v___x_1874_);
lean_ctor_set(v___x_1902_, 0, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_nextMacroScope_1893_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_ngen_1894_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_auxDeclNGen_1895_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v_traceState_1896_);
lean_ctor_set(v_reuseFailAlloc_1984_, 5, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1984_, 6, v_recordedDeps_1897_);
lean_ctor_set(v_reuseFailAlloc_1984_, 7, v_messages_1898_);
lean_ctor_set(v_reuseFailAlloc_1984_, 8, v_infoState_1899_);
lean_ctor_set(v_reuseFailAlloc_1984_, 9, v_snapshotTasks_1900_);
v___x_1906_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_mctx_1909_; lean_object* v_zetaDeltaFVarIds_1910_; lean_object* v_postponed_1911_; lean_object* v_diag_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1982_; 
v___x_1907_ = lean_st_ref_put(v___y_1838_, v___x_1906_);
v___x_1908_ = lean_st_ref_take(v___y_1836_);
v_mctx_1909_ = lean_ctor_get(v___x_1908_, 0);
v_zetaDeltaFVarIds_1910_ = lean_ctor_get(v___x_1908_, 2);
v_postponed_1911_ = lean_ctor_get(v___x_1908_, 3);
v_diag_1912_ = lean_ctor_get(v___x_1908_, 4);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1908_, 1);
lean_dec(v_unused_1983_);
v___x_1914_ = v___x_1908_;
v_isShared_1915_ = v_isSharedCheck_1982_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_diag_1912_);
lean_inc(v_postponed_1911_);
lean_inc(v_zetaDeltaFVarIds_1910_);
lean_inc(v_mctx_1909_);
lean_dec(v___x_1908_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1982_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1886_);
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_mctx_1909_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_zetaDeltaFVarIds_1910_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_postponed_1911_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_diag_1912_);
v___x_1917_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_env_1920_; lean_object* v_nextMacroScope_1921_; lean_object* v_ngen_1922_; lean_object* v_auxDeclNGen_1923_; lean_object* v_traceState_1924_; lean_object* v_recordedDeps_1925_; lean_object* v_messages_1926_; lean_object* v_infoState_1927_; lean_object* v_snapshotTasks_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1979_; 
v___x_1918_ = lean_st_ref_put(v___y_1836_, v___x_1917_);
v___x_1919_ = lean_st_ref_take(v___y_1838_);
v_env_1920_ = lean_ctor_get(v___x_1919_, 0);
v_nextMacroScope_1921_ = lean_ctor_get(v___x_1919_, 1);
v_ngen_1922_ = lean_ctor_get(v___x_1919_, 2);
v_auxDeclNGen_1923_ = lean_ctor_get(v___x_1919_, 3);
v_traceState_1924_ = lean_ctor_get(v___x_1919_, 4);
v_recordedDeps_1925_ = lean_ctor_get(v___x_1919_, 6);
v_messages_1926_ = lean_ctor_get(v___x_1919_, 7);
v_infoState_1927_ = lean_ctor_get(v___x_1919_, 8);
v_snapshotTasks_1928_ = lean_ctor_get(v___x_1919_, 9);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___x_1919_, 5);
lean_dec(v_unused_1980_);
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1979_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_snapshotTasks_1928_);
lean_inc(v_infoState_1927_);
lean_inc(v_messages_1926_);
lean_inc(v_recordedDeps_1925_);
lean_inc(v_traceState_1924_);
lean_inc(v_auxDeclNGen_1923_);
lean_inc(v_ngen_1922_);
lean_inc(v_nextMacroScope_1921_);
lean_inc(v_env_1920_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1979_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_numParams_1932_; lean_object* v_numIndices_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v_numParams_1932_ = lean_ctor_get(v___y_1832_, 1);
lean_inc(v_numParams_1932_);
v_numIndices_1933_ = lean_ctor_get(v___y_1832_, 2);
lean_inc(v_numIndices_1933_);
lean_dec_ref(v___y_1832_);
v___x_1934_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v_numParams_1932_, v___x_1935_);
lean_dec(v_numParams_1932_);
v___x_1937_ = lean_nat_add(v___x_1936_, v_numIndices_1933_);
lean_dec(v_numIndices_1933_);
lean_dec(v___x_1936_);
v___x_1938_ = lean_nat_add(v___x_1937_, v___x_1935_);
v___x_1939_ = lean_array_get_size(v_ctors_1812_);
v___x_1940_ = lean_nat_add(v___x_1938_, v___x_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_nat_add(v___x_1940_, v___x_1935_);
lean_dec(v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1942_, 0, v_indName_1811_);
lean_ctor_set(v___x_1942_, 1, v___x_1937_);
lean_ctor_set(v___x_1942_, 2, v___x_1941_);
lean_ctor_set(v___x_1942_, 3, v_ctors_1812_);
lean_inc(v___y_1830_);
v___x_1943_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1934_, v_env_1920_, v___y_1830_, v___x_1942_, v___y_1833_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 5, v___x_1874_);
lean_ctor_set(v___x_1930_, 0, v___x_1943_);
v___x_1945_ = v___x_1930_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_nextMacroScope_1921_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_ngen_1922_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_auxDeclNGen_1923_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v_traceState_1924_);
lean_ctor_set(v_reuseFailAlloc_1978_, 5, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1978_, 6, v_recordedDeps_1925_);
lean_ctor_set(v_reuseFailAlloc_1978_, 7, v_messages_1926_);
lean_ctor_set(v_reuseFailAlloc_1978_, 8, v_infoState_1927_);
lean_ctor_set(v_reuseFailAlloc_1978_, 9, v_snapshotTasks_1928_);
v___x_1945_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_mctx_1948_; lean_object* v_zetaDeltaFVarIds_1949_; lean_object* v_postponed_1950_; lean_object* v_diag_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1976_; 
v___x_1946_ = lean_st_ref_put(v___y_1838_, v___x_1945_);
v___x_1947_ = lean_st_ref_take(v___y_1836_);
v_mctx_1948_ = lean_ctor_get(v___x_1947_, 0);
v_zetaDeltaFVarIds_1949_ = lean_ctor_get(v___x_1947_, 2);
v_postponed_1950_ = lean_ctor_get(v___x_1947_, 3);
v_diag_1951_ = lean_ctor_get(v___x_1947_, 4);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v___x_1947_, 1);
lean_dec(v_unused_1977_);
v___x_1953_ = v___x_1947_;
v_isShared_1954_ = v_isSharedCheck_1976_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_diag_1951_);
lean_inc(v_postponed_1950_);
lean_inc(v_zetaDeltaFVarIds_1949_);
lean_inc(v_mctx_1948_);
lean_dec(v___x_1947_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1976_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 1, v___x_1886_);
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_mctx_1948_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_zetaDeltaFVarIds_1949_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_postponed_1950_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_diag_1951_);
v___x_1956_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_st_ref_put(v___y_1836_, v___x_1956_);
lean_inc(v___y_1830_);
v___x_1958_ = l_Lean_enableRealizationsForConst(v___y_1830_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1966_);
v___x_1960_ = v___x_1958_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v___x_1958_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___y_1830_);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___y_1830_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v___y_1830_);
v_a_1967_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1958_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1958_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
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
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v___y_1834_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v_a_1993_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1858_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1858_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec(v_a_1847_);
lean_dec_ref_known(v___x_1839_, 2);
lean_dec_ref(v___y_1834_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v_a_2003_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1848_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1848_);
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
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref_known(v___x_1839_, 2);
lean_dec_ref(v___y_1834_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v_a_2011_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1846_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1846_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec(v___x_1839_);
lean_dec_ref(v___y_1834_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v___x_2019_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__0, &l_Lean_Meta_mkSparseCasesOn___closed__0_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__0);
v___x_2020_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(v___x_2019_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_2020_;
}
}
v___jp_2021_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_inc(v_indName_1811_);
v___x_2034_ = l_Lean_mkCasesOnName(v_indName_1811_);
lean_inc(v___x_2034_);
v___x_2035_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(v___x_2034_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_toConstantVal_2036_; lean_object* v_a_2037_; lean_object* v_numParams_2038_; lean_object* v_numIndices_2039_; lean_object* v_ctors_2040_; lean_object* v_levelParams_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_toConstantVal_2036_ = lean_ctor_get(v___y_2022_, 0);
v_a_2037_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2035_, 1);
v_numParams_2038_ = lean_ctor_get(v___y_2022_, 1);
lean_inc(v_numParams_2038_);
v_numIndices_2039_ = lean_ctor_get(v___y_2022_, 2);
lean_inc(v_numIndices_2039_);
v_ctors_2040_ = lean_ctor_get(v___y_2022_, 4);
lean_inc(v_ctors_2040_);
v_levelParams_2041_ = lean_ctor_get(v_toConstantVal_2036_, 1);
lean_inc(v_indName_1811_);
v___x_2042_ = l_Lean_mkCtorIdxName(v_indName_1811_);
v___x_2043_ = l_Lean_ConstantInfo_levelParams(v_a_2037_);
v___x_2044_ = l_List_lengthTR___redArg(v___x_2043_);
lean_dec(v___x_2043_);
v___x_2045_ = l_List_lengthTR___redArg(v_levelParams_2041_);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_add(v___x_2045_, v___x_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_nat_dec_eq(v___x_2044_, v___x_2047_);
lean_dec(v___x_2047_);
lean_dec(v___x_2044_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v___x_2042_);
lean_dec(v_ctors_2040_);
lean_dec(v_numIndices_2039_);
lean_dec(v_numParams_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v___x_2049_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__2, &l_Lean_Meta_mkSparseCasesOn___closed__2_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__2);
v___x_2050_ = l_Lean_MessageData_ofConstName(v___x_2034_, v___x_2048_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_2053_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
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
else
{
lean_inc(v_a_2037_);
v___y_1820_ = v_a_2037_;
v___y_1821_ = v___x_2034_;
v___y_1822_ = v___x_2042_;
v___y_1823_ = v_numIndices_2039_;
v___y_1824_ = v___y_2023_;
v___y_1825_ = v_ctors_2040_;
v___y_1826_ = v_numParams_2038_;
v___y_1827_ = v___y_2024_;
v___y_1828_ = v_a_2037_;
v___y_1829_ = v___y_2025_;
v___y_1830_ = v___y_2026_;
v___y_1831_ = v___y_2027_;
v___y_1832_ = v___y_2022_;
v___y_1833_ = v___y_2028_;
v___y_1834_ = v___y_2029_;
v___y_1835_ = v___y_2030_;
v___y_1836_ = v___y_2031_;
v___y_1837_ = v___y_2032_;
v___y_1838_ = v___y_2033_;
goto v___jp_1819_;
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v___x_2034_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v_a_2063_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2035_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2035_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v_asyncMode_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2076_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
v_asyncMode_2077_ = lean_ctor_get(v___x_2076_, 2);
lean_inc_ref(v_ctors_1812_);
lean_inc(v_indName_1811_);
v___x_2078_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2078_, 0, v_indName_1811_);
lean_ctor_set(v___x_2078_, 1, v_ctors_1812_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*2, v___y_2075_);
v___x_2079_ = lean_box(0);
v___x_2080_ = 0;
v___x_2081_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2071_, v___x_2076_, v_env_2073_, v_asyncMode_2077_, v___x_2079_, v___x_2080_);
v___x_2082_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_2081_, v___x_2078_);
lean_dec(v___x_2081_);
if (lean_obj_tag(v___x_2082_) == 1)
{
lean_object* v_val_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v_val_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_val_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 0);
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_val_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_a_2093_; lean_object* v___f_2094_; lean_object* v___x_2095_; 
lean_dec(v___x_2082_);
v___x_2091_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__5));
v___x_2092_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v___x_2091_, v_a_1816_);
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc_n(v_a_2093_, 2);
lean_dec_ref(v___x_2092_);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__0), 3, 2);
lean_closure_set(v___f_2094_, 0, v___x_2078_);
lean_closure_set(v___f_2094_, 1, v_a_2093_);
lean_inc(v_indName_1811_);
v___x_2095_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_indName_1811_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; size_t v_sz_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = lean_box(0);
v_sz_2098_ = lean_array_size(v_ctors_1812_);
v___x_2099_ = ((size_t)0ULL);
lean_inc(v_indName_1811_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(v_a_2096_, v_indName_1811_, v_ctors_1812_, v_sz_2098_, v___x_2099_, v___x_2097_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_ctors_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
lean_dec_ref_known(v___x_2100_, 1);
v_ctors_2101_ = lean_ctor_get(v_a_2096_, 4);
v___x_2102_ = lean_array_get_size(v_ctors_1812_);
v___x_2103_ = l_List_lengthTR___redArg(v_ctors_2101_);
v___x_2104_ = lean_nat_dec_eq(v___x_2102_, v___x_2103_);
lean_dec(v___x_2103_);
if (v___x_2104_ == 0)
{
v___y_2022_ = v_a_2096_;
v___y_2023_ = v___x_2080_;
v___y_2024_ = v_asyncMode_2077_;
v___y_2025_ = v___x_2076_;
v___y_2026_ = v_a_2093_;
v___y_2027_ = v___x_2079_;
v___y_2028_ = v___x_2080_;
v___y_2029_ = v___f_2094_;
v___y_2030_ = v_a_1813_;
v___y_2031_ = v_a_1814_;
v___y_2032_ = v_a_1815_;
v___y_2033_ = v_a_1816_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_a_2096_);
lean_dec_ref(v___f_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v___x_2105_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__7, &l_Lean_Meta_mkSparseCasesOn___closed__7_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__7);
v___x_2106_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_2105_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_a_2096_);
lean_dec_ref(v___f_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v_a_2115_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2100_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2100_);
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
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v___f_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_ctors_1812_);
lean_dec(v_indName_1811_);
v_a_2123_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2095_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2095_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object* v_indName_2135_, lean_object* v_ctors_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Meta_mkSparseCasesOn(v_indName_2135_, v_ctors_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object* v_00_u03b2_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_2144_, v_x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object* v_00_u03b2_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(v_00_u03b2_2147_, v_x_2148_, v_x_2149_);
lean_dec_ref(v_x_2149_);
lean_dec_ref(v_x_2148_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object* v_00_u03b2_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_x_2152_, v_x_2153_, v_x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(lean_object* v_00_u03b1_2156_, lean_object* v_name_2157_, uint8_t v_bi_2158_, lean_object* v_type_2159_, lean_object* v_k_2160_, uint8_t v_kind_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_2157_, v_bi_2158_, v_type_2159_, v_k_2160_, v_kind_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2168_, lean_object* v_name_2169_, lean_object* v_bi_2170_, lean_object* v_type_2171_, lean_object* v_k_2172_, lean_object* v_kind_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v_bi_boxed_2179_; uint8_t v_kind_boxed_2180_; lean_object* v_res_2181_; 
v_bi_boxed_2179_ = lean_unbox(v_bi_2170_);
v_kind_boxed_2180_ = lean_unbox(v_kind_2173_);
v_res_2181_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(v_00_u03b1_2168_, v_name_2169_, v_bi_boxed_2179_, v_type_2171_, v_k_2172_, v_kind_boxed_2180_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object* v_00_u03b1_2182_, lean_object* v_name_2183_, lean_object* v_type_2184_, lean_object* v_k_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v_name_2183_, v_type_2184_, v_k_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_name_2193_, lean_object* v_type_2194_, lean_object* v_k_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_00_u03b1_2192_, v_name_2193_, v_type_2194_, v_k_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object* v_00_u03b1_2202_, lean_object* v_msg_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object* v_00_u03b1_2210_, lean_object* v_msg_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(v_00_u03b1_2210_, v_msg_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(lean_object* v_declName_2218_, uint8_t v_s_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_2218_, v_s_2219_, v___y_2221_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___boxed(lean_object* v_declName_2226_, lean_object* v_s_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v_s_boxed_2233_; lean_object* v_res_2234_; 
v_s_boxed_2233_ = lean_unbox(v_s_2227_);
v_res_2234_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(v_declName_2226_, v_s_boxed_2233_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object* v_00_u03b2_2235_, lean_object* v_x_2236_, size_t v_x_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_2236_, v_x_2237_, v_x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2240_, lean_object* v_x_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_){
_start:
{
size_t v_x_24641__boxed_2244_; lean_object* v_res_2245_; 
v_x_24641__boxed_2244_ = lean_unbox_usize(v_x_2242_);
lean_dec(v_x_2242_);
v_res_2245_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_2240_, v_x_2241_, v_x_24641__boxed_2244_, v_x_2243_);
lean_dec_ref(v_x_2243_);
lean_dec_ref(v_x_2241_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object* v_00_u03b2_2246_, lean_object* v_x_2247_, size_t v_x_2248_, size_t v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2247_, v_x_2248_, v_x_2249_, v_x_2250_, v_x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2253_, lean_object* v_x_2254_, lean_object* v_x_2255_, lean_object* v_x_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
size_t v_x_24652__boxed_2259_; size_t v_x_24653__boxed_2260_; lean_object* v_res_2261_; 
v_x_24652__boxed_2259_ = lean_unbox_usize(v_x_2255_);
lean_dec(v_x_2255_);
v_x_24653__boxed_2260_ = lean_unbox_usize(v_x_2256_);
lean_dec(v_x_2256_);
v_res_2261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_2253_, v_x_2254_, v_x_24652__boxed_2259_, v_x_24653__boxed_2260_, v_x_2257_, v_x_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(lean_object* v_00_u03b1_2262_, lean_object* v_constName_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_constName_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(v_00_u03b1_2270_, v_constName_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_2278_, lean_object* v_keys_2279_, lean_object* v_vals_2280_, lean_object* v_heq_2281_, lean_object* v_i_2282_, lean_object* v_k_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_keys_2279_, v_vals_2280_, v_i_2282_, v_k_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___boxed(lean_object* v_00_u03b2_2285_, lean_object* v_keys_2286_, lean_object* v_vals_2287_, lean_object* v_heq_2288_, lean_object* v_i_2289_, lean_object* v_k_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(v_00_u03b2_2285_, v_keys_2286_, v_vals_2287_, v_heq_2288_, v_i_2289_, v_k_2290_);
lean_dec_ref(v_k_2290_);
lean_dec_ref(v_vals_2287_);
lean_dec_ref(v_keys_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2292_, lean_object* v_n_2293_, lean_object* v_k_2294_, lean_object* v_v_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_n_2293_, v_k_2294_, v_v_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(lean_object* v_00_u03b2_2297_, size_t v_depth_2298_, lean_object* v_keys_2299_, lean_object* v_vals_2300_, lean_object* v_heq_2301_, lean_object* v_i_2302_, lean_object* v_entries_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_depth_2298_, v_keys_2299_, v_vals_2300_, v_i_2302_, v_entries_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___boxed(lean_object* v_00_u03b2_2305_, lean_object* v_depth_2306_, lean_object* v_keys_2307_, lean_object* v_vals_2308_, lean_object* v_heq_2309_, lean_object* v_i_2310_, lean_object* v_entries_2311_){
_start:
{
size_t v_depth_boxed_2312_; lean_object* v_res_2313_; 
v_depth_boxed_2312_ = lean_unbox_usize(v_depth_2306_);
lean_dec(v_depth_2306_);
v_res_2313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(v_00_u03b2_2305_, v_depth_boxed_2312_, v_keys_2307_, v_vals_2308_, v_heq_2309_, v_i_2310_, v_entries_2311_);
lean_dec_ref(v_vals_2308_);
lean_dec_ref(v_keys_2307_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(lean_object* v_00_u03b1_2314_, lean_object* v_ref_2315_, lean_object* v_constName_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_2315_, v_constName_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___boxed(lean_object* v_00_u03b1_2323_, lean_object* v_ref_2324_, lean_object* v_constName_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(v_00_u03b1_2323_, v_ref_2324_, v_constName_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v_ref_2324_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27(lean_object* v_00_u03b2_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(v_x_2333_, v_x_2334_, v_x_2335_, v_x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v_declHint_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_2339_, v_msg_2340_, v_declHint_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___boxed(lean_object* v_00_u03b1_2348_, lean_object* v_ref_2349_, lean_object* v_msg_2350_, lean_object* v_declHint_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(v_00_u03b1_2348_, v_ref_2349_, v_msg_2350_, v_declHint_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_ref_2349_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(lean_object* v_msg_2358_, lean_object* v_declHint_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_2358_, v_declHint_2359_, v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___boxed(lean_object* v_msg_2366_, lean_object* v_declHint_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(v_msg_2366_, v_declHint_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(lean_object* v_00_u03b1_2374_, lean_object* v_ref_2375_, lean_object* v_msg_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_2375_, v_msg_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_ref_2384_, lean_object* v_msg_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(v_00_u03b1_2383_, v_ref_2384_, v_msg_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v_ref_2384_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object* v_env_2392_, lean_object* v_sparseCasesOnName_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v_toEnvExtension_2395_; lean_object* v_asyncMode_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; 
v___x_2394_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2395_ = lean_ctor_get(v___x_2394_, 0);
v_asyncMode_2396_ = lean_ctor_get(v_toEnvExtension_2395_, 2);
v___x_2397_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2398_ = 0;
v___x_2399_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2397_, v___x_2394_, v_env_2392_, v_sparseCasesOnName_2393_, v_asyncMode_2396_, v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object* v_sparseCasesOnName_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v_env_2405_; lean_object* v___x_2406_; lean_object* v_toEnvExtension_2407_; lean_object* v_asyncMode_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2403_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2404_ = lean_st_ref_get(v_a_2401_);
v_env_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc_ref(v_env_2405_);
lean_dec(v___x_2404_);
v___x_2406_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2407_ = lean_ctor_get(v___x_2406_, 0);
v_asyncMode_2408_ = lean_ctor_get(v_toEnvExtension_2407_, 2);
v___x_2409_ = 0;
v___x_2410_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2403_, v___x_2406_, v_env_2405_, v_sparseCasesOnName_2400_, v_asyncMode_2408_, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object* v_sparseCasesOnName_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2412_, v_a_2413_);
lean_dec(v_a_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object* v_sparseCasesOnName_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2416_, v_a_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object* v_sparseCasesOnName_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
return v_res_2425_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
}
#ifdef __cplusplus
}
#endif
