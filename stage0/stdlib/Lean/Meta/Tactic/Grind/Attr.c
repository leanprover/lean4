// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Grind.Homo public import Lean.Meta.Sym.DSimp.Rewrite import Lean.Meta.Sym.Simp.Attr import Lean.ExtraModUses
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_addEntry(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_mkEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpTheoremFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "norm"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 82, 242, 154, 5, 26, 236, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 98, 249, 2, 230, 183, 10, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 254, 122, 13, 209, 4, 96, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 171, 221, 227, 25, 133, 195, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 72, 241, 93, 31, 88, 24, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 99, 64, 101, 196, 242, 78, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 102, 233, 244, 63, 110, 171, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 38, 22, 238, 56, 195, 101, 225)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 32, 197, 231, 9, 105, 134, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 8, 248, 216, 120, 97, 211, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 115, 203, 254, 31, 135, 121, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 182, 250, 113, 105, 31, 65, 165)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 202, 156, 167, 66, 153, 39, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 187, 236, 120, 172, 89, 32, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(448808965) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(24, 160, 99, 55, 202, 33, 244, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 159, 216, 39, 51, 61, 141, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 73, 198, 215, 12, 41, 81, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(146, 108, 201, 9, 220, 24, 56, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedNormSymEntry;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymTheorems_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "normSymExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 33, 18, 12, 138, 185, 216, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_NormSymTheorems_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSymExt;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "skipping `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, not a global declaration"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "skipping unfold `"};
static const lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindHom"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value),LEAN_SCALAR_PTR_LITERAL(14, 226, 234, 13, 148, 139, 225, 180)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindHomFallback"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value),LEAN_SCALAR_PTR_LITERAL(140, 210, 151, 50, 71, 98, 251, 189)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the modifier `usr` is only relevant in parameters for `grind only`"};
static const lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "cannot mark declaration to be unfolded by `grind`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "When applied to an equational theorem, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " =]`, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " =_]`, or `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = " _=_]`will mark the theorem for use in heuristic instantiations by the `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "` tactic,\n      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = " =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = " ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem\n      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 190, .m_capacity = 190, .m_length = 187, .m_data = " →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses\n      (that is, it will use the theorem for forwards reasoning).The attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "]` by itself will effectively try `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 68, .m_data = " ←]` (if the conclusion is sufficient for instantiation) and then `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 162, .m_data = " →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 179, .m_capacity = 179, .m_length = 178, .m_data = " =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "The `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "]` attribute is used to annotate declarations."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "!\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "!]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 161, 226, 116, 111, 153, 146, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "liaExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 224, 62, 90, 13, 174, 224, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liaExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_94_ = 0;
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_96_ = l_Lean_registerTraceClass(v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2____boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
return v_res_98_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__1);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_NameSet_empty;
v___x_105_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__3);
v___x_108_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__2);
v___x_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
lean_ctor_set(v___x_109_, 2, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_tag_nat(v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl___boxed(lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_Grind_NormSymEntry_ctorIdx___impl(v_x_114_);
lean_dec_ref(v_x_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(lean_object* v_t_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_thm_118_; lean_object* v___x_119_; 
v_thm_118_ = lean_ctor_get(v_t_116_, 0);
lean_inc_ref(v_thm_118_);
lean_dec_ref(v_t_116_);
v___x_119_ = lean_apply_1(v_k_117_, v_thm_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim(lean_object* v_motive_120_, lean_object* v_ctorIdx_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_k_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_122_, v_k_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_ctorElim___boxed(lean_object* v_motive_126_, lean_object* v_ctorIdx_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_k_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim(v_motive_126_, v_ctorIdx_127_, v_t_128_, v_h_129_, v_k_130_);
lean_dec(v_ctorIdx_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim___redArg(lean_object* v_t_132_, lean_object* v_pre_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_132_, v_pre_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_pre_elim(lean_object* v_motive_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_pre_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_136_, v_pre_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim___redArg(lean_object* v_t_140_, lean_object* v_post_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_140_, v_post_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_post_elim(lean_object* v_motive_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_post_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_144_, v_post_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim___redArg(lean_object* v_t_148_, lean_object* v_dsimp_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_148_, v_dsimp_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymEntry_dsimp_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_dsimp_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_NormSymEntry_ctorElim___redArg(v_t_152_, v_dsimp_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default___closed__0);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_instInhabitedNormSymEntry_default;
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSymTheorems_addEntry(lean_object* v_s_160_, lean_object* v_x_161_){
_start:
{
switch(lean_obj_tag(v_x_161_))
{
case 0:
{
lean_object* v_thm_162_; lean_object* v_pre_163_; lean_object* v_post_164_; lean_object* v_dsimp_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_thm_162_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_thm_162_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_163_ = lean_ctor_get(v_s_160_, 0);
v_post_164_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_165_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_173_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v_s_160_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_dsimp_165_);
lean_inc(v_post_164_);
lean_inc(v_pre_163_);
lean_dec(v_s_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_pre_163_, v_thm_162_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_post_164_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_dsimp_165_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
case 1:
{
lean_object* v_thm_174_; lean_object* v_pre_175_; lean_object* v_post_176_; lean_object* v_dsimp_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_thm_174_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_thm_174_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_175_ = lean_ctor_get(v_s_160_, 0);
v_post_176_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_177_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v_s_160_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_dsimp_177_);
lean_inc(v_post_176_);
lean_inc(v_pre_175_);
lean_dec(v_s_160_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_post_176_, v_thm_174_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_pre_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_dsimp_177_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
default: 
{
lean_object* v_entry_186_; lean_object* v_pre_187_; lean_object* v_post_188_; lean_object* v_dsimp_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_197_; 
v_entry_186_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_entry_186_);
lean_dec_ref_known(v_x_161_, 1);
v_pre_187_ = lean_ctor_get(v_s_160_, 0);
v_post_188_ = lean_ctor_get(v_s_160_, 1);
v_dsimp_189_ = lean_ctor_get(v_s_160_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_197_ == 0)
{
v___x_191_ = v_s_160_;
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_dsimp_189_);
lean_inc(v_post_188_);
lean_inc(v_pre_187_);
lean_dec(v_s_160_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_Meta_Sym_DSimp_Decls_addEntry(v_dsimp_189_, v_entry_186_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_pre_187_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_post_188_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(lean_object* v_x_198_){
_start:
{
lean_object* v_thm_200_; 
if (lean_obj_tag(v_x_198_) == 2)
{
lean_object* v_entry_205_; 
v_entry_205_ = lean_ctor_get(v_x_198_, 0);
lean_inc_ref(v_entry_205_);
lean_dec_ref_known(v_x_198_, 1);
if (lean_obj_tag(v_entry_205_) == 0)
{
lean_object* v_thm_206_; 
v_thm_206_ = lean_ctor_get(v_entry_205_, 0);
lean_inc_ref(v_thm_206_);
lean_dec_ref_known(v_entry_205_, 1);
v_thm_200_ = v_thm_206_;
goto v___jp_199_;
}
else
{
lean_object* v_declName_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_declName_207_ = lean_ctor_get(v_entry_205_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_entry_205_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v_entry_205_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_declName_207_);
lean_dec(v_entry_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_declName_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_thm_215_; 
v_thm_215_ = lean_ctor_get(v_x_198_, 0);
lean_inc_ref(v_thm_215_);
lean_dec_ref(v_x_198_);
v_thm_200_ = v_thm_215_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v_expr_201_; 
v_expr_201_ = lean_ctor_get(v_thm_200_, 0);
lean_inc_ref(v_expr_201_);
lean_dec_ref(v_thm_200_);
if (lean_obj_tag(v_expr_201_) == 4)
{
lean_object* v_declName_202_; lean_object* v___x_203_; 
v_declName_202_ = lean_ctor_get(v_expr_201_, 0);
lean_inc(v_declName_202_);
lean_dec_ref_known(v_expr_201_, 2);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_declName_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v_expr_201_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v_x_216_, lean_object* v_e_217_){
_start:
{
lean_object* v___x_218_; 
lean_inc_ref(v_e_217_);
v___x_218_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_NormSymEntry_declName_x3f(v_e_217_);
if (lean_obj_tag(v___x_218_) == 1)
{
lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_233_; 
v_val_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_233_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_233_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_isPrivateName(v_val_219_);
lean_dec(v_val_219_);
if (v___x_223_ == 0)
{
lean_object* v___x_225_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_e_217_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_e_217_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
lean_inc_ref_n(v___x_225_, 2);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
lean_ctor_set(v___x_226_, 2, v___x_225_);
return v___x_226_;
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_e_217_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_e_217_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_228_);
lean_ctor_set(v___x_231_, 1, v___x_228_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
return v___x_231_;
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v___x_218_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_e_217_);
lean_inc_ref_n(v___x_234_, 2);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_x_236_, lean_object* v_e_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v_x_236_, v_e_237_);
lean_dec_ref(v_x_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(lean_object* v___y_239_){
_start:
{
lean_inc_ref(v___y_239_);
return v___y_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(v___y_240_);
lean_dec_ref(v___y_240_);
return v_res_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_251_ = lean_box(0);
v___x_252_ = 0;
v___f_253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___f_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_255_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__4);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_));
v___x_258_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_255_);
lean_ctor_set(v___x_258_, 3, v___f_254_);
lean_ctor_set(v___x_258_, 4, v___f_253_);
lean_ctor_set(v___x_258_, 5, v___x_251_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*6, v___x_252_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*6 + 1, v___x_252_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_);
v___x_261_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2____boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(lean_object* v_____r_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___closed__0));
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0___boxed(lean_object* v_____r_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_____r_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; uint8_t v___x_289_; lean_object* v_env_290_; lean_object* v___x_291_; lean_object* v_toCold_292_; lean_object* v_mctx_293_; lean_object* v_lctx_294_; lean_object* v_options_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_287_ = lean_st_ref_get(v___y_285_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_env_288_);
lean_dec(v___x_287_);
v___x_289_ = 0;
v_env_290_ = l_Lean_Environment_setRecordingDeps(v_env_288_, v___x_289_);
v___x_291_ = lean_st_ref_get(v___y_283_);
v_toCold_292_ = lean_ctor_get(v___y_284_, 0);
v_mctx_293_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_mctx_293_);
lean_dec(v___x_291_);
v_lctx_294_ = lean_ctor_get(v___y_282_, 2);
v_options_295_ = lean_ctor_get(v_toCold_292_, 2);
lean_inc_ref(v_options_295_);
lean_inc_ref(v_lctx_294_);
v___x_296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_296_, 0, v_env_290_);
lean_ctor_set(v___x_296_, 1, v_mctx_293_);
lean_ctor_set(v___x_296_, 2, v_lctx_294_);
lean_ctor_set(v___x_296_, 3, v_options_295_);
v___x_297_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_msgData_281_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msgData_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_306_; double v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_float_of_nat(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(lean_object* v_cls_311_, lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_365_; 
v_ref_318_ = lean_ctor_get(v___y_315_, 2);
v___x_319_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_365_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_365_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_365_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v_traceState_325_; lean_object* v_env_326_; lean_object* v_nextMacroScope_327_; lean_object* v_ngen_328_; lean_object* v_auxDeclNGen_329_; lean_object* v_cache_330_; lean_object* v_recordedDeps_331_; lean_object* v_messages_332_; lean_object* v_infoState_333_; lean_object* v_snapshotTasks_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_364_; 
v___x_324_ = lean_st_ref_take(v___y_316_);
v_traceState_325_ = lean_ctor_get(v___x_324_, 4);
v_env_326_ = lean_ctor_get(v___x_324_, 0);
v_nextMacroScope_327_ = lean_ctor_get(v___x_324_, 1);
v_ngen_328_ = lean_ctor_get(v___x_324_, 2);
v_auxDeclNGen_329_ = lean_ctor_get(v___x_324_, 3);
v_cache_330_ = lean_ctor_get(v___x_324_, 5);
v_recordedDeps_331_ = lean_ctor_get(v___x_324_, 6);
v_messages_332_ = lean_ctor_get(v___x_324_, 7);
v_infoState_333_ = lean_ctor_get(v___x_324_, 8);
v_snapshotTasks_334_ = lean_ctor_get(v___x_324_, 9);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_364_ == 0)
{
v___x_336_ = v___x_324_;
v_isShared_337_ = v_isSharedCheck_364_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snapshotTasks_334_);
lean_inc(v_infoState_333_);
lean_inc(v_messages_332_);
lean_inc(v_recordedDeps_331_);
lean_inc(v_cache_330_);
lean_inc(v_traceState_325_);
lean_inc(v_auxDeclNGen_329_);
lean_inc(v_ngen_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_env_326_);
lean_dec(v___x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_364_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint64_t v_tid_338_; lean_object* v_traces_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_363_; 
v_tid_338_ = lean_ctor_get_uint64(v_traceState_325_, sizeof(void*)*1);
v_traces_339_ = lean_ctor_get(v_traceState_325_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_traceState_325_);
if (v_isSharedCheck_363_ == 0)
{
v___x_341_ = v_traceState_325_;
v_isShared_342_ = v_isSharedCheck_363_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_traces_339_);
lean_dec(v_traceState_325_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_363_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; double v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_box(0);
v___x_345_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_346_ = 0;
v___x_347_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_348_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_348_, 0, v_cls_311_);
lean_ctor_set(v___x_348_, 1, v___x_344_);
lean_ctor_set(v___x_348_, 2, v___x_347_);
lean_ctor_set_float(v___x_348_, sizeof(void*)*3, v___x_345_);
lean_ctor_set_float(v___x_348_, sizeof(void*)*3 + 8, v___x_345_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*3 + 16, v___x_346_);
v___x_349_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_350_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v_a_320_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_inc(v_ref_318_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_ref_318_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_PersistentArray_push___redArg(v_traces_339_, v___x_351_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_352_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_352_);
lean_ctor_set_uint64(v_reuseFailAlloc_362_, sizeof(void*)*1, v_tid_338_);
v___x_354_ = v_reuseFailAlloc_362_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v___x_354_);
v___x_356_ = v___x_336_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_env_326_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_ngen_328_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_auxDeclNGen_329_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_361_, 5, v_cache_330_);
lean_ctor_set(v_reuseFailAlloc_361_, 6, v_recordedDeps_331_);
lean_ctor_set(v_reuseFailAlloc_361_, 7, v_messages_332_);
lean_ctor_set(v_reuseFailAlloc_361_, 8, v_infoState_333_);
lean_ctor_set(v_reuseFailAlloc_361_, 9, v_snapshotTasks_334_);
v___x_356_ = v_reuseFailAlloc_361_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_st_ref_put(v___y_316_, v___x_356_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_343_);
v___x_359_ = v___x_322_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_343_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___boxed(lean_object* v_cls_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_366_, v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_379_ = l_Lean_Name_append(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__3));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__5));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__7));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(lean_object* v_thm_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___y_396_; lean_object* v_proof_409_; 
v_proof_409_ = lean_ctor_get(v_thm_389_, 2);
if (lean_obj_tag(v_proof_409_) == 4)
{
lean_object* v_declName_410_; lean_object* v___x_414_; 
lean_inc_ref(v_proof_409_);
lean_dec_ref(v_thm_389_);
v_declName_410_ = lean_ctor_get(v_proof_409_, 0);
lean_inc_n(v_declName_410_, 2);
lean_dec_ref_known(v_proof_409_, 2);
v___x_414_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_410_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_declName_410_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_461_; 
v_a_424_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_461_ == 0)
{
v___x_426_ = v___x_414_;
v_isShared_427_ = v_isSharedCheck_461_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_461_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_Exception_isInterrupt(v_a_424_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
lean_inc(v_a_424_);
v___x_429_ = l_Lean_Exception_isRuntime(v_a_424_);
if (v___x_429_ == 0)
{
lean_object* v_toCold_430_; lean_object* v_options_431_; uint8_t v_hasTrace_432_; 
lean_del_object(v___x_426_);
v_toCold_430_ = lean_ctor_get(v_a_392_, 0);
v_options_431_ = lean_ctor_get(v_toCold_430_, 2);
v_hasTrace_432_ = lean_ctor_get_uint8(v_options_431_, sizeof(void*)*1);
if (v_hasTrace_432_ == 0)
{
lean_dec(v_a_424_);
lean_dec(v_declName_410_);
goto v___jp_411_;
}
else
{
lean_object* v_inheritedTraceOptions_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_inheritedTraceOptions_433_ = lean_ctor_get(v_toCold_430_, 11);
v___x_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_433_, v_options_431_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v_a_424_);
lean_dec(v_declName_410_);
goto v___jp_411_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_438_ = l_Lean_MessageData_ofConstName(v_declName_410_, v___x_429_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Lean_Exception_toMessageData(v_a_424_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_434_, v___x_443_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v_a_445_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
v___y_396_ = v___x_446_;
goto v___jp_395_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_a_447_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_444_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_444_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_declName_410_);
if (v_isShared_427_ == 0)
{
v___x_456_ = v___x_426_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_424_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v_declName_410_);
if (v_isShared_427_ == 0)
{
v___x_459_ = v___x_426_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_424_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
v___jp_411_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_box(0);
v___x_413_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___lam__0(v___x_412_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
v___y_396_ = v___x_413_;
goto v___jp_395_;
}
}
else
{
lean_object* v_toCold_462_; lean_object* v_options_463_; uint8_t v_hasTrace_464_; 
v_toCold_462_ = lean_ctor_get(v_a_392_, 0);
v_options_463_ = lean_ctor_get(v_toCold_462_, 2);
v_hasTrace_464_ = lean_ctor_get_uint8(v_options_463_, sizeof(void*)*1);
if (v_hasTrace_464_ == 0)
{
lean_dec_ref(v_thm_389_);
goto v___jp_406_;
}
else
{
lean_object* v_origin_465_; lean_object* v_inheritedTraceOptions_466_; lean_object* v_cls_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_origin_465_ = lean_ctor_get(v_thm_389_, 4);
lean_inc_ref(v_origin_465_);
lean_dec_ref(v_thm_389_);
v_inheritedTraceOptions_466_ = lean_ctor_get(v_toCold_462_, 11);
v_cls_467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_469_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_466_, v_options_463_, v___x_468_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_origin_465_);
goto v___jp_406_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__4);
v___x_471_ = l_Lean_Meta_Origin_key(v_origin_465_);
lean_dec_ref(v_origin_465_);
v___x_472_ = l_Lean_MessageData_ofName(v___x_471_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_470_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__8);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_467_, v___x_475_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_dec_ref_known(v___x_476_, 1);
goto v___jp_406_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
}
v___jp_395_:
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_a_397_ = lean_ctor_get(v___y_396_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___y_396_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v___y_396_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___y_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_a_401_; lean_object* v___x_403_; 
v_a_401_ = lean_ctor_get(v_a_397_, 0);
lean_inc(v_a_401_);
lean_dec(v_a_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_a_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
v___jp_406_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___boxed(lean_object* v_thm_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_thm_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object* v___y_492_, uint8_t v_isExporting_493_, lean_object* v___x_494_, lean_object* v___y_495_, lean_object* v___x_496_, lean_object* v_a_x3f_497_){
_start:
{
lean_object* v___x_499_; lean_object* v_env_500_; lean_object* v_nextMacroScope_501_; lean_object* v_ngen_502_; lean_object* v_auxDeclNGen_503_; lean_object* v_traceState_504_; lean_object* v_recordedDeps_505_; lean_object* v_messages_506_; lean_object* v_infoState_507_; lean_object* v_snapshotTasks_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_533_; 
v___x_499_ = lean_st_ref_take(v___y_492_);
v_env_500_ = lean_ctor_get(v___x_499_, 0);
v_nextMacroScope_501_ = lean_ctor_get(v___x_499_, 1);
v_ngen_502_ = lean_ctor_get(v___x_499_, 2);
v_auxDeclNGen_503_ = lean_ctor_get(v___x_499_, 3);
v_traceState_504_ = lean_ctor_get(v___x_499_, 4);
v_recordedDeps_505_ = lean_ctor_get(v___x_499_, 6);
v_messages_506_ = lean_ctor_get(v___x_499_, 7);
v_infoState_507_ = lean_ctor_get(v___x_499_, 8);
v_snapshotTasks_508_ = lean_ctor_get(v___x_499_, 9);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v___x_499_, 5);
lean_dec(v_unused_534_);
v___x_510_ = v___x_499_;
v_isShared_511_ = v_isSharedCheck_533_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snapshotTasks_508_);
lean_inc(v_infoState_507_);
lean_inc(v_messages_506_);
lean_inc(v_recordedDeps_505_);
lean_inc(v_traceState_504_);
lean_inc(v_auxDeclNGen_503_);
lean_inc(v_ngen_502_);
lean_inc(v_nextMacroScope_501_);
lean_inc(v_env_500_);
lean_dec(v___x_499_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_533_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = l_Lean_Environment_setExporting(v_env_500_, v_isExporting_493_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 5, v___x_494_);
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_ngen_502_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_auxDeclNGen_503_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_traceState_504_);
lean_ctor_set(v_reuseFailAlloc_532_, 5, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_532_, 6, v_recordedDeps_505_);
lean_ctor_set(v_reuseFailAlloc_532_, 7, v_messages_506_);
lean_ctor_set(v_reuseFailAlloc_532_, 8, v_infoState_507_);
lean_ctor_set(v_reuseFailAlloc_532_, 9, v_snapshotTasks_508_);
v___x_514_ = v_reuseFailAlloc_532_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_mctx_517_; lean_object* v_zetaDeltaFVarIds_518_; lean_object* v_postponed_519_; lean_object* v_diag_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_530_; 
v___x_515_ = lean_st_ref_put(v___y_492_, v___x_514_);
v___x_516_ = lean_st_ref_take(v___y_495_);
v_mctx_517_ = lean_ctor_get(v___x_516_, 0);
v_zetaDeltaFVarIds_518_ = lean_ctor_get(v___x_516_, 2);
v_postponed_519_ = lean_ctor_get(v___x_516_, 3);
v_diag_520_ = lean_ctor_get(v___x_516_, 4);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v___x_516_, 1);
lean_dec(v_unused_531_);
v___x_522_ = v___x_516_;
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_diag_520_);
lean_inc(v_postponed_519_);
lean_inc(v_zetaDeltaFVarIds_518_);
lean_inc(v_mctx_517_);
lean_dec(v___x_516_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_496_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_mctx_517_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_zetaDeltaFVarIds_518_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v_postponed_519_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v_diag_520_);
v___x_526_ = v_reuseFailAlloc_529_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_st_ref_put(v___y_495_, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_524_);
return v___x_528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object* v___y_535_, lean_object* v_isExporting_536_, lean_object* v___x_537_, lean_object* v___y_538_, lean_object* v___x_539_, lean_object* v_a_x3f_540_, lean_object* v___y_541_){
_start:
{
uint8_t v_isExporting_boxed_542_; lean_object* v_res_543_; 
v_isExporting_boxed_542_ = lean_unbox(v_isExporting_536_);
v_res_543_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_535_, v_isExporting_boxed_542_, v___x_537_, v___y_538_, v___x_539_, v_a_x3f_540_);
lean_dec(v_a_x3f_540_);
lean_dec(v___y_538_);
lean_dec(v___y_535_);
return v_res_543_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__0);
v___x_549_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_ctor_set(v___x_549_, 2, v___x_548_);
lean_ctor_set(v___x_549_, 3, v___x_548_);
lean_ctor_set(v___x_549_, 4, v___x_548_);
lean_ctor_set(v___x_549_, 5, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object* v_x_550_, uint8_t v_isExporting_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; lean_object* v_env_558_; lean_object* v___x_559_; uint8_t v_isModule_560_; 
v___x_557_ = lean_st_ref_get(v___y_555_);
v_env_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc_ref(v_env_558_);
lean_dec(v___x_557_);
v___x_559_ = l_Lean_Environment_header(v_env_558_);
v_isModule_560_ = lean_ctor_get_uint8(v___x_559_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_559_);
if (v_isModule_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec_ref(v_env_558_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v___x_561_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
return v___x_561_;
}
else
{
uint8_t v_isExporting_562_; 
v_isExporting_562_ = lean_ctor_get_uint8(v_env_558_, sizeof(void*)*13);
lean_dec_ref(v_env_558_);
if (v_isExporting_551_ == 0)
{
if (v_isExporting_562_ == 0)
{
lean_object* v___x_629_; 
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v___x_629_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
return v___x_629_;
}
else
{
goto v___jp_563_;
}
}
else
{
if (v_isExporting_562_ == 0)
{
goto v___jp_563_;
}
else
{
lean_object* v___x_630_; 
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v___x_630_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
return v___x_630_;
}
}
v___jp_563_:
{
lean_object* v___x_564_; lean_object* v_env_565_; lean_object* v_nextMacroScope_566_; lean_object* v_ngen_567_; lean_object* v_auxDeclNGen_568_; lean_object* v_traceState_569_; lean_object* v_recordedDeps_570_; lean_object* v_messages_571_; lean_object* v_infoState_572_; lean_object* v_snapshotTasks_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_627_; 
v___x_564_ = lean_st_ref_take(v___y_555_);
v_env_565_ = lean_ctor_get(v___x_564_, 0);
v_nextMacroScope_566_ = lean_ctor_get(v___x_564_, 1);
v_ngen_567_ = lean_ctor_get(v___x_564_, 2);
v_auxDeclNGen_568_ = lean_ctor_get(v___x_564_, 3);
v_traceState_569_ = lean_ctor_get(v___x_564_, 4);
v_recordedDeps_570_ = lean_ctor_get(v___x_564_, 6);
v_messages_571_ = lean_ctor_get(v___x_564_, 7);
v_infoState_572_ = lean_ctor_get(v___x_564_, 8);
v_snapshotTasks_573_ = lean_ctor_get(v___x_564_, 9);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_564_, 5);
lean_dec(v_unused_628_);
v___x_575_ = v___x_564_;
v_isShared_576_ = v_isSharedCheck_627_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_snapshotTasks_573_);
lean_inc(v_infoState_572_);
lean_inc(v_messages_571_);
lean_inc(v_recordedDeps_570_);
lean_inc(v_traceState_569_);
lean_inc(v_auxDeclNGen_568_);
lean_inc(v_ngen_567_);
lean_inc(v_nextMacroScope_566_);
lean_inc(v_env_565_);
lean_dec(v___x_564_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_627_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = l_Lean_Environment_setExporting(v_env_565_, v_isExporting_551_);
v___x_578_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 5, v___x_578_);
lean_ctor_set(v___x_575_, 0, v___x_577_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_nextMacroScope_566_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_ngen_567_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_auxDeclNGen_568_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_traceState_569_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_recordedDeps_570_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_messages_571_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_infoState_572_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_snapshotTasks_573_);
v___x_580_ = v_reuseFailAlloc_626_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_mctx_583_; lean_object* v_zetaDeltaFVarIds_584_; lean_object* v_postponed_585_; lean_object* v_diag_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_624_; 
v___x_581_ = lean_st_ref_put(v___y_555_, v___x_580_);
v___x_582_ = lean_st_ref_take(v___y_553_);
v_mctx_583_ = lean_ctor_get(v___x_582_, 0);
v_zetaDeltaFVarIds_584_ = lean_ctor_get(v___x_582_, 2);
v_postponed_585_ = lean_ctor_get(v___x_582_, 3);
v_diag_586_ = lean_ctor_get(v___x_582_, 4);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_582_, 1);
lean_dec(v_unused_625_);
v___x_588_ = v___x_582_;
v_isShared_589_ = v_isSharedCheck_624_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_diag_586_);
lean_inc(v_postponed_585_);
lean_inc(v_zetaDeltaFVarIds_584_);
lean_inc(v_mctx_583_);
lean_dec(v___x_582_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_624_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_mctx_583_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_zetaDeltaFVarIds_584_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_postponed_585_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_diag_586_);
v___x_592_ = v_reuseFailAlloc_623_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v_r_594_; 
v___x_593_ = lean_st_ref_put(v___y_553_, v___x_592_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
v_r_594_ = lean_apply_5(v_x_550_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
if (lean_obj_tag(v_r_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_611_; 
v_a_595_ = lean_ctor_get(v_r_594_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_r_594_);
if (v_isSharedCheck_611_ == 0)
{
v___x_597_ = v_r_594_;
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v_r_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
lean_inc(v_a_595_);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_610_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v___x_601_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_555_, v_isExporting_562_, v___x_578_, v___y_553_, v___x_590_, v___x_600_);
lean_dec_ref(v___x_600_);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_609_);
v___x_603_ = v___x_601_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_dec(v___x_601_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_a_595_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_595_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_612_ = lean_ctor_get(v_r_594_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v_r_594_, 1);
v___x_613_ = lean_box(0);
v___x_614_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_555_, v_isExporting_562_, v___x_578_, v___y_553_, v___x_590_, v___x_613_);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_614_, 0);
lean_dec(v_unused_622_);
v___x_616_ = v___x_614_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_dec(v___x_614_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 1);
lean_ctor_set(v___x_616_, 0, v_a_612_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_612_);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object* v_x_631_, lean_object* v_isExporting_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v_isExporting_boxed_638_; lean_object* v_res_639_; 
v_isExporting_boxed_638_ = lean_unbox(v_isExporting_632_);
v_res_639_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_631_, v_isExporting_boxed_638_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object* v_00_u03b1_640_, lean_object* v_x_641_, uint8_t v_isExporting_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_641_, v_isExporting_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object* v_00_u03b1_649_, lean_object* v_x_650_, lean_object* v_isExporting_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_isExporting_boxed_657_; lean_object* v_res_658_; 
v_isExporting_boxed_657_ = lean_unbox(v_isExporting_651_);
v_res_658_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(v_00_u03b1_649_, v_x_650_, v_isExporting_boxed_657_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object* v_ext_659_, lean_object* v_b_660_, uint8_t v_kind_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_toCold_666_; lean_object* v_currNamespace_667_; lean_object* v___x_668_; lean_object* v_env_669_; lean_object* v_nextMacroScope_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_traceState_673_; lean_object* v_recordedDeps_674_; lean_object* v_messages_675_; lean_object* v_infoState_676_; lean_object* v_snapshotTasks_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_704_; 
v_toCold_666_ = lean_ctor_get(v___y_663_, 0);
v_currNamespace_667_ = lean_ctor_get(v_toCold_666_, 4);
v___x_668_ = lean_st_ref_take(v___y_664_);
v_env_669_ = lean_ctor_get(v___x_668_, 0);
v_nextMacroScope_670_ = lean_ctor_get(v___x_668_, 1);
v_ngen_671_ = lean_ctor_get(v___x_668_, 2);
v_auxDeclNGen_672_ = lean_ctor_get(v___x_668_, 3);
v_traceState_673_ = lean_ctor_get(v___x_668_, 4);
v_recordedDeps_674_ = lean_ctor_get(v___x_668_, 6);
v_messages_675_ = lean_ctor_get(v___x_668_, 7);
v_infoState_676_ = lean_ctor_get(v___x_668_, 8);
v_snapshotTasks_677_ = lean_ctor_get(v___x_668_, 9);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_668_, 5);
lean_dec(v_unused_705_);
v___x_679_ = v___x_668_;
v_isShared_680_ = v_isSharedCheck_704_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snapshotTasks_677_);
lean_inc(v_infoState_676_);
lean_inc(v_messages_675_);
lean_inc(v_recordedDeps_674_);
lean_inc(v_traceState_673_);
lean_inc(v_auxDeclNGen_672_);
lean_inc(v_ngen_671_);
lean_inc(v_nextMacroScope_670_);
lean_inc(v_env_669_);
lean_dec(v___x_668_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_704_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
lean_inc(v_currNamespace_667_);
v___x_681_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_669_, v_ext_659_, v_b_660_, v_kind_661_, v_currNamespace_667_);
v___x_682_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 5, v___x_682_);
lean_ctor_set(v___x_679_, 0, v___x_681_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_nextMacroScope_670_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_ngen_671_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_auxDeclNGen_672_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_traceState_673_);
lean_ctor_set(v_reuseFailAlloc_703_, 5, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_703_, 6, v_recordedDeps_674_);
lean_ctor_set(v_reuseFailAlloc_703_, 7, v_messages_675_);
lean_ctor_set(v_reuseFailAlloc_703_, 8, v_infoState_676_);
lean_ctor_set(v_reuseFailAlloc_703_, 9, v_snapshotTasks_677_);
v___x_684_ = v_reuseFailAlloc_703_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_mctx_687_; lean_object* v_zetaDeltaFVarIds_688_; lean_object* v_postponed_689_; lean_object* v_diag_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_701_; 
v___x_685_ = lean_st_ref_put(v___y_664_, v___x_684_);
v___x_686_ = lean_st_ref_take(v___y_662_);
v_mctx_687_ = lean_ctor_get(v___x_686_, 0);
v_zetaDeltaFVarIds_688_ = lean_ctor_get(v___x_686_, 2);
v_postponed_689_ = lean_ctor_get(v___x_686_, 3);
v_diag_690_ = lean_ctor_get(v___x_686_, 4);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_686_, 1);
lean_dec(v_unused_702_);
v___x_692_ = v___x_686_;
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_diag_690_);
lean_inc(v_postponed_689_);
lean_inc(v_zetaDeltaFVarIds_688_);
lean_inc(v_mctx_687_);
lean_dec(v___x_686_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = lean_box(0);
v___x_695_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_695_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_mctx_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_zetaDeltaFVarIds_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_postponed_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_diag_690_);
v___x_697_ = v_reuseFailAlloc_700_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_st_ref_put(v___y_662_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_694_);
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object* v_ext_706_, lean_object* v_b_707_, lean_object* v_kind_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v_kind_boxed_713_; lean_object* v_res_714_; 
v_kind_boxed_713_ = lean_unbox(v_kind_708_);
v_res_714_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_706_, v_b_707_, v_kind_boxed_713_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_00_u03c3_717_, lean_object* v_ext_718_, lean_object* v_b_719_, uint8_t v_kind_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_718_, v_b_719_, v_kind_720_, v___y_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_00_u03c3_729_, lean_object* v_ext_730_, lean_object* v_b_731_, lean_object* v_kind_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v_kind_boxed_738_; lean_object* v_res_739_; 
v_kind_boxed_738_ = lean_unbox(v_kind_732_);
v_res_739_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(v_00_u03b1_727_, v_00_u03b2_728_, v_00_u03c3_729_, v_ext_730_, v_b_731_, v_kind_boxed_738_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t v_attrKind_740_, uint8_t v_post_741_, lean_object* v_as_742_, size_t v_sz_743_, size_t v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_a_752_; uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_lt(v_i_744_, v_sz_743_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_745_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_758_ = lean_box(0);
v_a_759_ = lean_array_uget_borrowed(v_as_742_, v_i_744_);
v___x_760_ = l_Lean_Meta_Grind_normExt;
lean_inc(v_a_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v_a_759_);
v___x_762_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_760_, v___x_761_, v_attrKind_740_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_762_, 0);
lean_dec(v_unused_805_);
v___x_764_ = v___x_762_;
v_isShared_765_ = v_isSharedCheck_804_;
goto v_resetjp_763_;
}
else
{
lean_dec(v___x_762_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_804_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; 
lean_inc(v_a_759_);
v___x_766_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_a_759_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
if (lean_obj_tag(v_a_767_) == 1)
{
lean_object* v_val_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_795_; 
v_val_768_ = lean_ctor_get(v_a_767_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_767_);
if (v_isSharedCheck_795_ == 0)
{
v___x_770_ = v_a_767_;
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_val_768_);
lean_dec(v_a_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___y_774_; 
v___x_772_ = l_Lean_Meta_Grind_normSymExt;
if (v_post_741_ == 0)
{
lean_object* v___x_790_; 
lean_inc(v_val_768_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_val_768_);
v___x_790_ = v___x_764_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_768_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v___y_774_ = v___x_790_;
goto v___jp_773_;
}
}
else
{
lean_object* v___x_793_; 
lean_inc(v_val_768_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 0, v_val_768_);
v___x_793_ = v___x_764_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_val_768_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v___y_774_ = v___x_793_;
goto v___jp_773_;
}
}
v___jp_773_:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_772_, v___y_774_, v_attrKind_740_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_787_; 
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___x_775_, 0);
lean_dec(v_unused_788_);
v___x_777_ = v___x_775_;
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
else
{
lean_dec(v___x_775_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
if (v_post_741_ == 0)
{
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
lean_dec(v_val_768_);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
uint8_t v_rfl_779_; 
v_rfl_779_ = lean_ctor_get_uint8(v_a_759_, sizeof(void*)*5 + 2);
if (v_rfl_779_ == 0)
{
lean_del_object(v___x_777_);
lean_del_object(v___x_770_);
lean_dec(v_val_768_);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
lean_object* v___x_781_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_val_768_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_val_768_);
v___x_781_ = v_reuseFailAlloc_786_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 2);
lean_ctor_set(v___x_770_, 0, v___x_781_);
v___x_783_ = v___x_770_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_785_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_772_, v___x_783_, v_attrKind_740_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_dec_ref_known(v___x_784_, 1);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
return v___x_784_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_770_);
lean_dec(v_val_768_);
return v___x_775_;
}
}
}
}
else
{
lean_dec(v_a_767_);
lean_del_object(v___x_764_);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_del_object(v___x_764_);
v_a_796_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_766_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_766_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
return v___x_762_;
}
}
v___jp_751_:
{
size_t v___x_753_; size_t v___x_754_; 
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_744_, v___x_753_);
v_i_744_ = v___x_754_;
v_b_745_ = v_a_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object* v_attrKind_806_, lean_object* v_post_807_, lean_object* v_as_808_, lean_object* v_sz_809_, lean_object* v_i_810_, lean_object* v_b_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v_attrKind_boxed_817_; uint8_t v_post_boxed_818_; size_t v_sz_boxed_819_; size_t v_i_boxed_820_; lean_object* v_res_821_; 
v_attrKind_boxed_817_ = lean_unbox(v_attrKind_806_);
v_post_boxed_818_ = lean_unbox(v_post_807_);
v_sz_boxed_819_ = lean_unbox_usize(v_sz_809_);
lean_dec(v_sz_809_);
v_i_boxed_820_ = lean_unbox_usize(v_i_810_);
lean_dec(v_i_810_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_boxed_817_, v_post_boxed_818_, v_as_808_, v_sz_boxed_819_, v_i_boxed_820_, v_b_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v_as_808_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object* v_declName_822_, uint8_t v_post_823_, uint8_t v_inv_824_, uint8_t v_attrKind_825_, lean_object* v_prio_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___y_838_; uint8_t v___x_861_; uint8_t v___x_862_; 
v___x_832_ = 1;
v___x_833_ = lean_box(v_post_823_);
v___x_834_ = lean_box(v_inv_824_);
v___x_835_ = lean_box(v___x_832_);
lean_inc(v_declName_822_);
v___x_836_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpTheoremFromConst___boxed), 10, 5);
lean_closure_set(v___x_836_, 0, v_declName_822_);
lean_closure_set(v___x_836_, 1, v___x_833_);
lean_closure_set(v___x_836_, 2, v___x_834_);
lean_closure_set(v___x_836_, 3, v_prio_826_);
lean_closure_set(v___x_836_, 4, v___x_835_);
v___x_861_ = 1;
v___x_862_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_825_, v___x_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_isPrivateName(v_declName_822_);
lean_dec(v_declName_822_);
if (v___x_863_ == 0)
{
v___y_838_ = v___x_832_;
goto v___jp_837_;
}
else
{
v___y_838_ = v___x_862_;
goto v___jp_837_;
}
}
else
{
uint8_t v___x_864_; 
lean_dec(v_declName_822_);
v___x_864_ = 0;
v___y_838_ = v___x_864_;
goto v___jp_837_;
}
v___jp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v___x_836_, v___y_838_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; size_t v_sz_842_; size_t v___x_843_; lean_object* v___x_844_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = lean_box(0);
v_sz_842_ = lean_array_size(v_a_840_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_825_, v_post_823_, v_a_840_, v_sz_842_, v___x_843_, v___x_841_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_840_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v___x_844_, 0);
lean_dec(v_unused_852_);
v___x_846_ = v___x_844_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_dec(v___x_844_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_841_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_841_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
return v___x_844_;
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_839_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_839_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object* v_declName_865_, lean_object* v_post_866_, lean_object* v_inv_867_, lean_object* v_attrKind_868_, lean_object* v_prio_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
uint8_t v_post_boxed_875_; uint8_t v_inv_boxed_876_; uint8_t v_attrKind_boxed_877_; lean_object* v_res_878_; 
v_post_boxed_875_ = lean_unbox(v_post_866_);
v_inv_boxed_876_ = lean_unbox(v_inv_867_);
v_attrKind_boxed_877_ = lean_unbox(v_attrKind_868_);
v_res_878_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_865_, v_post_boxed_875_, v_inv_boxed_876_, v_attrKind_boxed_877_, v_prio_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t v_attrKind_879_, lean_object* v_as_880_, size_t v_sz_881_, size_t v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_lt(v_i_882_, v_sz_881_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v_b_883_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_890_ = lean_box(0);
v_a_891_ = lean_array_uget_borrowed(v_as_880_, v_i_882_);
v___x_892_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_891_);
v___x_893_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_893_, 0, v_a_891_);
v___x_894_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_892_, v___x_893_, v_attrKind_879_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_894_) == 0)
{
size_t v___x_895_; size_t v___x_896_; 
lean_dec_ref_known(v___x_894_, 1);
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_add(v_i_882_, v___x_895_);
v_i_882_ = v___x_896_;
v_b_883_ = v___x_890_;
goto _start;
}
else
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object* v_attrKind_898_, lean_object* v_as_899_, lean_object* v_sz_900_, lean_object* v_i_901_, lean_object* v_b_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_attrKind_boxed_907_; size_t v_sz_boxed_908_; size_t v_i_boxed_909_; lean_object* v_res_910_; 
v_attrKind_boxed_907_ = lean_unbox(v_attrKind_898_);
v_sz_boxed_908_ = lean_unbox_usize(v_sz_900_);
lean_dec(v_sz_900_);
v_i_boxed_909_ = lean_unbox_usize(v_i_901_);
lean_dec(v_i_901_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_boxed_907_, v_as_899_, v_sz_boxed_908_, v_i_boxed_909_, v_b_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v_as_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object* v_declName_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_env_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_914_ = lean_st_ref_get(v___y_912_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_ref(v_env_915_);
lean_dec(v___x_914_);
v___x_916_ = l_Lean_getReducibilityStatusCore(v_env_915_, v_declName_911_);
v___x_917_ = lean_box(v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object* v_declName_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_919_, v___y_920_);
lean_dec(v___y_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object* v_declName_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_945_; 
v___x_929_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_923_, v___y_927_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_945_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint8_t v___x_934_; 
v___x_934_ = lean_unbox(v_a_930_);
lean_dec(v_a_930_);
if (v___x_934_ == 0)
{
uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = 1;
v___x_936_ = lean_box(v___x_935_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_936_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = 0;
v___x_941_ = lean_box(v___x_940_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_941_);
v___x_943_ = v___x_932_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object* v_declName_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t v_attrKind_953_, lean_object* v_as_954_, size_t v_sz_955_, size_t v_i_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_lt(v_i_956_, v_sz_955_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_b_957_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_964_ = lean_box(0);
v_a_965_ = lean_array_uget_borrowed(v_as_954_, v_i_956_);
v___x_966_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_965_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_a_965_);
v___x_968_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_966_, v___x_967_, v_attrKind_953_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_968_) == 0)
{
size_t v___x_969_; size_t v___x_970_; 
lean_dec_ref_known(v___x_968_, 1);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_956_, v___x_969_);
v_i_956_ = v___x_970_;
v_b_957_ = v___x_964_;
goto _start;
}
else
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object* v_attrKind_972_, lean_object* v_as_973_, lean_object* v_sz_974_, lean_object* v_i_975_, lean_object* v_b_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_attrKind_boxed_981_; size_t v_sz_boxed_982_; size_t v_i_boxed_983_; lean_object* v_res_984_; 
v_attrKind_boxed_981_ = lean_unbox(v_attrKind_972_);
v_sz_boxed_982_ = lean_unbox_usize(v_sz_974_);
lean_dec(v_sz_974_);
v_i_boxed_983_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_boxed_981_, v_as_973_, v_sz_boxed_982_, v_i_boxed_983_, v_b_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v_as_973_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object* v_declName_988_, uint8_t v_attrKind_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_998_; 
lean_inc(v_declName_988_);
v___x_998_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1065_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1065_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1065_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___y_1004_; lean_object* v_a_1005_; uint8_t v___x_1024_; 
v___x_1024_ = lean_unbox(v_a_999_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_del_object(v___x_1001_);
lean_inc(v_declName_988_);
v___x_1025_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_declName_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; size_t v_sz_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = lean_box(0);
v_sz_1028_ = lean_array_size(v_a_1026_);
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_989_, v_a_1026_, v_sz_1028_, v___x_1029_, v___x_1027_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_1026_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref_known(v___x_1030_, 1);
lean_inc(v_declName_988_);
v___x_1031_ = l_Lean_Meta_Sym_DSimp_Decls_mkEntries(v_declName_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; size_t v_sz_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_sz_1033_ = lean_array_size(v_a_1032_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_989_, v_a_1032_, v_sz_1033_, v___x_1029_, v___x_1027_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v___x_1034_, 0);
lean_dec(v_unused_1042_);
v___x_1036_ = v___x_1034_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v___x_1034_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1027_);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1027_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v_a_1043_; 
v_a_1043_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1043_);
v___y_1004_ = v___x_1034_;
v_a_1005_ = v_a_1043_;
goto v___jp_1003_;
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1031_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1031_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
lean_inc(v_a_1044_);
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
v___y_1004_ = v___x_1049_;
v_a_1005_ = v_a_1044_;
goto v___jp_1003_;
}
}
}
}
else
{
lean_object* v_a_1052_; 
v_a_1052_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1052_);
v___y_1004_ = v___x_1030_;
v_a_1005_ = v_a_1052_;
goto v___jp_1003_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1025_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1025_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
lean_inc(v_a_1053_);
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
v___y_1004_ = v___x_1058_;
v_a_1005_ = v_a_1053_;
goto v___jp_1003_;
}
}
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
v___x_1061_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1061_);
v___x_1063_ = v___x_1001_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
v___jp_1003_:
{
uint8_t v___x_1006_; 
v___x_1006_ = l_Lean_Exception_isInterrupt(v_a_1005_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
lean_inc_ref(v_a_1005_);
v___x_1007_ = l_Lean_Exception_isRuntime(v_a_1005_);
if (v___x_1007_ == 0)
{
lean_object* v_toCold_1008_; lean_object* v_options_1009_; uint8_t v_hasTrace_1010_; 
lean_dec_ref(v___y_1004_);
v_toCold_1008_ = lean_ctor_get(v_a_992_, 0);
v_options_1009_ = lean_ctor_get(v_toCold_1008_, 2);
v_hasTrace_1010_ = lean_ctor_get_uint8(v_options_1009_, sizeof(void*)*1);
if (v_hasTrace_1010_ == 0)
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
goto v___jp_995_;
}
else
{
lean_object* v_inheritedTraceOptions_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_inheritedTraceOptions_1011_ = lean_ctor_get(v_toCold_1008_, 11);
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_1013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_1014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1011_, v_options_1009_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1015_ = lean_obj_once(&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1, &l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once, _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1);
v___x_1016_ = lean_unbox(v_a_999_);
lean_dec(v_a_999_);
v___x_1017_ = l_Lean_MessageData_ofConstName(v_declName_988_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1015_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_Exception_toMessageData(v_a_1005_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_1012_, v___x_1022_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1023_;
}
}
}
else
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
return v___y_1004_;
}
}
else
{
lean_dec_ref(v_a_1005_);
lean_dec(v_a_999_);
lean_dec(v_declName_988_);
return v___y_1004_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_declName_988_);
v_a_1066_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_998_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_998_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
v___jp_995_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object* v_declName_1074_, lean_object* v_attrKind_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
uint8_t v_attrKind_boxed_1081_; lean_object* v_res_1082_; 
v_attrKind_boxed_1081_ = lean_unbox(v_attrKind_1075_);
v_res_1082_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1074_, v_attrKind_boxed_1081_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object* v_declName_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_1083_, v___y_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object* v_declName_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(v_declName_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t v_attrKind_1097_, lean_object* v_as_1098_, size_t v_sz_1099_, size_t v_i_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1097_, v_as_1098_, v_sz_1099_, v_i_1100_, v_b_1101_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object* v_attrKind_1108_, lean_object* v_as_1109_, lean_object* v_sz_1110_, lean_object* v_i_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_attrKind_boxed_1118_; size_t v_sz_boxed_1119_; size_t v_i_boxed_1120_; lean_object* v_res_1121_; 
v_attrKind_boxed_1118_ = lean_unbox(v_attrKind_1108_);
v_sz_boxed_1119_ = lean_unbox_usize(v_sz_1110_);
lean_dec(v_sz_1110_);
v_i_boxed_1120_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(v_attrKind_boxed_1118_, v_as_1109_, v_sz_boxed_1119_, v_i_boxed_1120_, v_b_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_as_1109_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t v_attrKind_1122_, lean_object* v_as_1123_, size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1122_, v_as_1123_, v_sz_1124_, v_i_1125_, v_b_1126_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object* v_attrKind_1133_, lean_object* v_as_1134_, lean_object* v_sz_1135_, lean_object* v_i_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_attrKind_boxed_1143_; size_t v_sz_boxed_1144_; size_t v_i_boxed_1145_; lean_object* v_res_1146_; 
v_attrKind_boxed_1143_ = lean_unbox(v_attrKind_1133_);
v_sz_boxed_1144_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1145_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(v_attrKind_boxed_1143_, v_as_1134_, v_sz_boxed_1144_, v_i_boxed_1145_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_as_1134_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object* v_declName_1147_, uint8_t v_attrKind_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = l_Lean_Meta_Grind_normExt;
v___x_1155_ = 0;
v___x_1156_ = lean_unsigned_to_nat(1000u);
lean_inc(v_declName_1147_);
v___x_1157_ = l_Lean_Meta_addDeclToUnfold(v___x_1154_, v_declName_1147_, v___x_1155_, v___x_1155_, v___x_1156_, v_attrKind_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1184_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1184_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1184_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_unbox(v_a_1158_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_a_1158_);
lean_dec(v_declName_1147_);
v___x_1163_ = lean_box(v___x_1155_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1163_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
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
lean_object* v___x_1167_; 
lean_del_object(v___x_1160_);
v___x_1167_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1147_, v_attrKind_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v___x_1167_, 0);
lean_dec(v_unused_1175_);
v___x_1169_ = v___x_1167_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_dec(v___x_1167_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v_a_1158_);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1158_);
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
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_a_1158_);
v_a_1176_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1167_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_1147_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object* v_declName_1185_, lean_object* v_attrKind_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_attrKind_boxed_1192_; lean_object* v_res_1193_; 
v_attrKind_boxed_1192_ = lean_unbox(v_attrKind_1186_);
v_res_1193_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_1185_, v_attrKind_boxed_1192_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_obj_tag_nat(v_x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object* v_x_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(v_x_1196_);
lean_dec(v_x_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
switch(lean_obj_tag(v_t_1198_))
{
case 0:
{
lean_object* v_k_1200_; lean_object* v___x_1201_; 
v_k_1200_ = lean_ctor_get(v_t_1198_, 0);
lean_inc(v_k_1200_);
lean_dec_ref_known(v_t_1198_, 1);
v___x_1201_ = lean_apply_1(v_k_1199_, v_k_1200_);
return v___x_1201_;
}
case 1:
{
uint8_t v_eager_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_eager_1202_ = lean_ctor_get_uint8(v_t_1198_, 0);
lean_dec_ref_known(v_t_1198_, 0);
v___x_1203_ = lean_box(v_eager_1202_);
v___x_1204_ = lean_apply_1(v_k_1199_, v___x_1203_);
return v___x_1204_;
}
case 5:
{
lean_object* v_prio_1205_; lean_object* v___x_1206_; 
v_prio_1205_ = lean_ctor_get(v_t_1198_, 0);
lean_inc(v_prio_1205_);
lean_dec_ref_known(v_t_1198_, 1);
v___x_1206_ = lean_apply_1(v_k_1199_, v_prio_1205_);
return v___x_1206_;
}
case 8:
{
uint8_t v_post_1207_; uint8_t v_inv_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_post_1207_ = lean_ctor_get_uint8(v_t_1198_, 0);
v_inv_1208_ = lean_ctor_get_uint8(v_t_1198_, 1);
lean_dec_ref_known(v_t_1198_, 0);
v___x_1209_ = lean_box(v_post_1207_);
v___x_1210_ = lean_box(v_inv_1208_);
v___x_1211_ = lean_apply_2(v_k_1199_, v___x_1209_, v___x_1210_);
return v___x_1211_;
}
case 10:
{
uint8_t v_fallback_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_fallback_1212_ = lean_ctor_get_uint8(v_t_1198_, 0);
lean_dec_ref_known(v_t_1198_, 0);
v___x_1213_ = lean_box(v_fallback_1212_);
v___x_1214_ = lean_apply_1(v_k_1199_, v___x_1213_);
return v___x_1214_;
}
default: 
{
lean_dec(v_t_1198_);
return v_k_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_1215_, lean_object* v_ctorIdx_1216_, lean_object* v_t_1217_, lean_object* v_h_1218_, lean_object* v_k_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1217_, v_k_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_1221_, lean_object* v_ctorIdx_1222_, lean_object* v_t_1223_, lean_object* v_h_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_1221_, v_ctorIdx_1222_, v_t_1223_, v_h_1224_, v_k_1225_);
lean_dec(v_ctorIdx_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_1227_, lean_object* v_ematch_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1227_, v_ematch_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_1230_, lean_object* v_t_1231_, lean_object* v_h_1232_, lean_object* v_ematch_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1231_, v_ematch_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_1235_, lean_object* v_cases_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1235_, v_cases_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_1238_, lean_object* v_t_1239_, lean_object* v_h_1240_, lean_object* v_cases_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1239_, v_cases_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_1243_, lean_object* v_intro_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1243_, v_intro_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_1246_, lean_object* v_t_1247_, lean_object* v_h_1248_, lean_object* v_intro_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1247_, v_intro_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_1251_, lean_object* v_infer_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1251_, v_infer_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_1254_, lean_object* v_t_1255_, lean_object* v_h_1256_, lean_object* v_infer_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1255_, v_infer_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_1259_, lean_object* v_ext_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1259_, v_ext_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_1262_, lean_object* v_t_1263_, lean_object* v_h_1264_, lean_object* v_ext_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1263_, v_ext_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_1267_, lean_object* v_symbol_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1267_, v_symbol_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_1270_, lean_object* v_t_1271_, lean_object* v_h_1272_, lean_object* v_symbol_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1271_, v_symbol_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_1275_, lean_object* v_inj_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1275_, v_inj_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_1278_, lean_object* v_t_1279_, lean_object* v_h_1280_, lean_object* v_inj_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1279_, v_inj_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_1283_, lean_object* v_funCC_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1283_, v_funCC_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_1286_, lean_object* v_t_1287_, lean_object* v_h_1288_, lean_object* v_funCC_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1287_, v_funCC_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_1291_, lean_object* v_norm_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1291_, v_norm_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_1294_, lean_object* v_t_1295_, lean_object* v_h_1296_, lean_object* v_norm_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1295_, v_norm_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_1299_, lean_object* v_unfold_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1299_, v_unfold_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_1302_, lean_object* v_t_1303_, lean_object* v_h_1304_, lean_object* v_unfold_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1303_, v_unfold_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_1307_, lean_object* v_homo_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1307_, v_homo_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_1310_, lean_object* v_t_1311_, lean_object* v_h_1312_, lean_object* v_homo_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1311_, v_homo_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_1315_, lean_object* v_homoPred_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1315_, v_homoPred_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_1318_, lean_object* v_t_1319_, lean_object* v_h_1320_, lean_object* v_homoPred_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1319_, v_homoPred_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1326_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_ctor_set(v___x_1328_, 3, v___x_1327_);
lean_ctor_set(v___x_1328_, 4, v___x_1326_);
lean_ctor_set(v___x_1328_, 5, v___x_1326_);
lean_ctor_set(v___x_1328_, 6, v___x_1326_);
lean_ctor_set(v___x_1328_, 7, v___x_1326_);
lean_ctor_set(v___x_1328_, 8, v___x_1326_);
lean_ctor_set(v___x_1328_, 9, v___x_1326_);
lean_ctor_set(v___x_1328_, 10, v___x_1326_);
lean_ctor_set(v___x_1328_, 11, v___x_1325_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(32u);
v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1332_ = ((size_t)5ULL);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_unsigned_to_nat(32u);
v___x_1335_ = lean_mk_empty_array_with_capacity(v___x_1334_);
v___x_1336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_1337_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v___x_1333_);
lean_ctor_set(v___x_1337_, 3, v___x_1333_);
lean_ctor_set_usize(v___x_1337_, 4, v___x_1332_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1338_ = lean_box(1);
v___x_1339_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_1340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___x_1339_);
lean_ctor_set(v___x_1341_, 2, v___x_1338_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v_toCold_1347_; lean_object* v_env_1348_; lean_object* v_options_1349_; uint8_t v___x_1350_; lean_object* v_env_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1346_ = lean_st_ref_get(v___y_1344_);
v_toCold_1347_ = lean_ctor_get(v___y_1343_, 0);
v_env_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc_ref(v_env_1348_);
lean_dec(v___x_1346_);
v_options_1349_ = lean_ctor_get(v_toCold_1347_, 2);
v___x_1350_ = 0;
v_env_1351_ = l_Lean_Environment_setRecordingDeps(v_env_1348_, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_1353_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_1349_);
v___x_1354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1354_, 0, v_env_1351_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
lean_ctor_set(v___x_1354_, 2, v___x_1353_);
lean_ctor_set(v___x_1354_, 3, v_options_1349_);
v___x_1355_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_msgData_1342_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_ref_1366_; lean_object* v___x_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_ref_1366_ = lean_ctor_get(v___y_1363_, 2);
v___x_1367_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_1362_, v___y_1363_, v___y_1364_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc(v_ref_1366_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_ref_1366_);
lean_ctor_set(v___x_1372_, 1, v_a_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 1);
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_1382_, lean_object* v_msg_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_toCold_1387_; lean_object* v_currRecDepth_1388_; lean_object* v_ref_1389_; uint16_t v_optionFlags_1390_; uint8_t v_suppressElabErrors_1391_; uint8_t v_isRecordingDeps_1392_; lean_object* v_ref_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_toCold_1387_ = lean_ctor_get(v___y_1384_, 0);
v_currRecDepth_1388_ = lean_ctor_get(v___y_1384_, 1);
v_ref_1389_ = lean_ctor_get(v___y_1384_, 2);
v_optionFlags_1390_ = lean_ctor_get_uint16(v___y_1384_, sizeof(void*)*3);
v_suppressElabErrors_1391_ = lean_ctor_get_uint8(v___y_1384_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1392_ = lean_ctor_get_uint8(v___y_1384_, sizeof(void*)*3 + 3);
v_ref_1393_ = l_Lean_replaceRef(v_ref_1382_, v_ref_1389_);
lean_inc(v_currRecDepth_1388_);
lean_inc_ref(v_toCold_1387_);
v___x_1394_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1394_, 0, v_toCold_1387_);
lean_ctor_set(v___x_1394_, 1, v_currRecDepth_1388_);
lean_ctor_set(v___x_1394_, 2, v_ref_1393_);
lean_ctor_set_uint16(v___x_1394_, sizeof(void*)*3, v_optionFlags_1390_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*3 + 2, v_suppressElabErrors_1391_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*3 + 3, v_isRecordingDeps_1392_);
v___x_1395_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1383_, v___x_1394_, v___y_1385_);
lean_dec_ref_known(v___x_1394_, 3);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_1396_, lean_object* v_msg_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1396_, v_msg_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v_ref_1396_);
return v_res_1401_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__5));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__2));
lean_inc(v_stx_1582_);
v___x_1587_ = l_Lean_Syntax_isOfKind(v_stx_1582_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1588_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1589_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1592_, v_a_1583_, v_a_1584_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = l_Lean_Syntax_getArg(v_stx_1582_, v___x_1594_);
v___x_1596_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__8));
lean_inc(v___x_1595_);
v___x_1597_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__10));
lean_inc(v___x_1595_);
v___x_1599_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__12));
lean_inc(v___x_1595_);
v___x_1601_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__14));
lean_inc(v___x_1595_);
v___x_1603_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__16));
lean_inc(v___x_1595_);
v___x_1605_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__18));
lean_inc(v___x_1595_);
v___x_1607_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__20));
lean_inc(v___x_1595_);
v___x_1609_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__22));
lean_inc(v___x_1595_);
v___x_1611_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__24));
lean_inc(v___x_1595_);
v___x_1613_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__26));
lean_inc(v___x_1595_);
v___x_1615_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
lean_inc(v___x_1595_);
v___x_1617_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__30));
lean_inc(v___x_1595_);
v___x_1619_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__32));
lean_inc(v___x_1595_);
v___x_1621_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__34));
lean_inc(v___x_1595_);
v___x_1623_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__36));
lean_inc(v___x_1595_);
v___x_1625_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__38));
lean_inc(v___x_1595_);
v___x_1627_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__40));
lean_inc(v___x_1595_);
v___x_1629_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__42));
lean_inc(v___x_1595_);
v___x_1631_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__44));
lean_inc(v___x_1595_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__46));
lean_inc(v___x_1595_);
v___x_1635_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__48));
lean_inc(v___x_1595_);
v___x_1637_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__50));
lean_inc(v___x_1595_);
v___x_1639_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
lean_inc(v___x_1595_);
v___x_1641_ = l_Lean_Syntax_isOfKind(v___x_1595_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v___x_1595_);
v___x_1642_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1643_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1646_, v_a_1583_, v_a_1584_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_stx_1582_);
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1648_);
lean_dec(v___x_1595_);
v___x_1650_ = l_Lean_Syntax_isNatLit_x3f(v___x_1649_);
if (lean_obj_tag(v___x_1650_) == 1)
{
lean_object* v_val_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v___x_1649_);
v_val_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_val_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 5);
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_val_1651_);
v___x_1656_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v___x_1650_);
v___x_1660_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__54, &l_Lean_Meta_Grind_getAttrKindCore___closed__54_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54);
v___x_1661_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_1649_, v___x_1660_, v_a_1583_, v_a_1584_);
lean_dec(v___x_1649_);
return v___x_1661_;
}
}
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1662_ = lean_box(11);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1664_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1664_, 0, v___x_1587_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1666_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1666_, 0, v___x_1633_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1668_ = lean_box(9);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1670_);
lean_inc(v___x_1671_);
v___x_1672_ = l_Lean_Syntax_matchesNull(v___x_1671_, v___x_1594_);
if (v___x_1672_ == 0)
{
uint8_t v___x_1673_; 
lean_inc(v___x_1671_);
v___x_1673_ = l_Lean_Syntax_matchesNull(v___x_1671_, v___x_1670_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1671_);
lean_dec(v___x_1595_);
v___x_1674_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1675_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1678_, v_a_1583_, v_a_1584_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1680_ = l_Lean_Syntax_getArg(v___x_1671_, v___x_1594_);
lean_dec(v___x_1671_);
v___x_1681_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_1680_);
v___x_1682_ = l_Lean_Syntax_isOfKind(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_1684_ = l_Lean_Syntax_isOfKind(v___x_1680_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v___x_1595_);
v___x_1685_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1686_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1689_, v_a_1583_, v_a_1584_);
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = lean_unsigned_to_nat(2u);
v___x_1692_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1691_);
lean_dec(v___x_1595_);
lean_inc(v___x_1692_);
v___x_1693_ = l_Lean_Syntax_matchesNull(v___x_1692_, v___x_1594_);
if (v___x_1693_ == 0)
{
uint8_t v___x_1694_; 
v___x_1694_ = l_Lean_Syntax_matchesNull(v___x_1692_, v___x_1670_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1695_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1696_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1699_, v_a_1583_, v_a_1584_);
return v___x_1700_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec(v_stx_1582_);
v___x_1701_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1701_, 0, v___x_1693_);
lean_ctor_set_uint8(v___x_1701_, 1, v___x_1587_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v___x_1692_);
lean_dec(v_stx_1582_);
v___x_1703_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1703_, 0, v___x_1682_);
lean_ctor_set_uint8(v___x_1703_, 1, v___x_1682_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
lean_dec(v___x_1680_);
v___x_1705_ = lean_unsigned_to_nat(2u);
v___x_1706_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1705_);
lean_dec(v___x_1595_);
lean_inc(v___x_1706_);
v___x_1707_ = l_Lean_Syntax_matchesNull(v___x_1706_, v___x_1594_);
if (v___x_1707_ == 0)
{
uint8_t v___x_1708_; 
v___x_1708_ = l_Lean_Syntax_matchesNull(v___x_1706_, v___x_1670_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1709_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1710_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1713_, v_a_1583_, v_a_1584_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec(v_stx_1582_);
v___x_1715_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1715_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1715_, 1, v___x_1587_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v___x_1706_);
lean_dec(v_stx_1582_);
v___x_1717_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1717_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1717_, 1, v___x_1672_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
}
}
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
lean_dec(v___x_1671_);
v___x_1719_ = lean_unsigned_to_nat(2u);
v___x_1720_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1719_);
lean_dec(v___x_1595_);
lean_inc(v___x_1720_);
v___x_1721_ = l_Lean_Syntax_matchesNull(v___x_1720_, v___x_1594_);
if (v___x_1721_ == 0)
{
uint8_t v___x_1722_; 
v___x_1722_ = l_Lean_Syntax_matchesNull(v___x_1720_, v___x_1670_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1723_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1724_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1727_, v_a_1583_, v_a_1584_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_stx_1582_);
v___x_1729_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1729_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1729_, 1, v___x_1587_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v___x_1720_);
lean_dec(v_stx_1582_);
v___x_1731_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1731_, 0, v___x_1587_);
lean_ctor_set_uint8(v___x_1731_, 1, v___x_1629_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1733_ = lean_box(7);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1735_ = lean_box(6);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1737_ = lean_box(4);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1739_ = lean_box(2);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1741_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1741_, 0, v___x_1587_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1743_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1743_, 0, v___x_1617_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1745_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1745_, 0, v___x_1587_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1748_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1750_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1752_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1754_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1756_ = lean_unsigned_to_nat(3u);
v___x_1757_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1756_);
lean_dec(v___x_1595_);
lean_inc(v___x_1757_);
v___x_1758_ = l_Lean_Syntax_matchesNull(v___x_1757_, v___x_1594_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1757_);
v___x_1760_ = l_Lean_Syntax_matchesNull(v___x_1757_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v___x_1757_);
v___x_1761_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1762_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1765_, v_a_1583_, v_a_1584_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1767_ = l_Lean_Syntax_getArg(v___x_1757_, v___x_1594_);
lean_dec(v___x_1757_);
v___x_1768_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1769_ = l_Lean_Syntax_isOfKind(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1770_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1771_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1774_, v_a_1583_, v_a_1584_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec(v_stx_1582_);
v___x_1776_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1776_, 0, v___x_1587_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v___x_1757_);
lean_dec(v_stx_1582_);
v___x_1779_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1779_, 0, v___x_1605_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_unsigned_to_nat(2u);
v___x_1783_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1782_);
lean_dec(v___x_1595_);
lean_inc(v___x_1783_);
v___x_1784_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___x_1594_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1783_);
v___x_1786_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec(v___x_1783_);
v___x_1787_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1788_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1791_, v_a_1583_, v_a_1584_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = l_Lean_Syntax_getArg(v___x_1783_, v___x_1594_);
lean_dec(v___x_1783_);
v___x_1794_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1795_ = l_Lean_Syntax_isOfKind(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1796_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1797_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1800_, v_a_1583_, v_a_1584_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v_stx_1582_);
v___x_1802_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1802_, 0, v___x_1587_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec(v___x_1783_);
lean_dec(v_stx_1582_);
v___x_1805_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1805_, 0, v___x_1603_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1808_);
lean_dec(v___x_1595_);
lean_inc(v___x_1809_);
v___x_1810_ = l_Lean_Syntax_matchesNull(v___x_1809_, v___x_1594_);
if (v___x_1810_ == 0)
{
uint8_t v___x_1811_; 
lean_inc(v___x_1809_);
v___x_1811_ = l_Lean_Syntax_matchesNull(v___x_1809_, v___x_1808_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v___x_1809_);
v___x_1812_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1813_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1816_, v_a_1583_, v_a_1584_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = l_Lean_Syntax_getArg(v___x_1809_, v___x_1594_);
lean_dec(v___x_1809_);
v___x_1819_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1820_ = l_Lean_Syntax_isOfKind(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1821_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1822_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1825_, v_a_1583_, v_a_1584_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v_stx_1582_);
v___x_1827_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1827_, 0, v___x_1587_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v___x_1809_);
lean_dec(v_stx_1582_);
v___x_1830_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1830_, 0, v___x_1601_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v___x_1595_);
lean_dec(v_stx_1582_);
v___x_1833_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1835_);
lean_dec(v___x_1595_);
lean_inc(v___x_1836_);
v___x_1837_ = l_Lean_Syntax_matchesNull(v___x_1836_, v___x_1594_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
lean_inc(v___x_1836_);
v___x_1838_ = l_Lean_Syntax_matchesNull(v___x_1836_, v___x_1835_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v___x_1836_);
v___x_1839_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1840_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1843_, v_a_1583_, v_a_1584_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = l_Lean_Syntax_getArg(v___x_1836_, v___x_1594_);
lean_dec(v___x_1836_);
v___x_1846_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1847_ = l_Lean_Syntax_isOfKind(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1848_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1849_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1852_, v_a_1583_, v_a_1584_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v_stx_1582_);
v___x_1854_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1854_, 0, v___x_1587_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec(v___x_1836_);
lean_dec(v_stx_1582_);
v___x_1857_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1857_, 0, v___x_1597_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = l_Lean_Syntax_getArg(v___x_1595_, v___x_1860_);
lean_dec(v___x_1595_);
lean_inc(v___x_1861_);
v___x_1862_ = l_Lean_Syntax_matchesNull(v___x_1861_, v___x_1594_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; 
lean_inc(v___x_1861_);
v___x_1863_ = l_Lean_Syntax_matchesNull(v___x_1861_, v___x_1860_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec(v___x_1861_);
v___x_1864_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1865_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1868_, v_a_1583_, v_a_1584_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1870_ = l_Lean_Syntax_getArg(v___x_1861_, v___x_1594_);
lean_dec(v___x_1861_);
v___x_1871_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1872_ = l_Lean_Syntax_isOfKind(v___x_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1873_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1874_ = l_Lean_MessageData_ofSyntax(v_stx_1582_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1877_, v_a_1583_, v_a_1584_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec(v_stx_1582_);
v___x_1879_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1879_, 0, v___x_1587_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v___x_1861_);
lean_dec(v_stx_1582_);
v___x_1882_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_1884_, v_a_1885_, v_a_1886_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_1889_, lean_object* v_msg_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_1895_, lean_object* v_msg_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_1895_, v_msg_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_1901_, lean_object* v_ref_1902_, lean_object* v_msg_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1902_, v_msg_1903_, v___y_1904_, v___y_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_1908_, lean_object* v_ref_1909_, lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_1908_, v_ref_1909_, v_msg_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v_ref_1909_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = l_Lean_Syntax_getArg(v_stx_1915_, v___x_1919_);
v___x_1921_ = l_Lean_Syntax_isNone(v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = l_Lean_Syntax_getArg(v___x_1920_, v___x_1922_);
lean_dec(v___x_1920_);
v___x_1924_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_1923_, v_a_1916_, v_a_1917_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec(v___x_1920_);
v___x_1925_ = lean_box(3);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_1927_, v_a_1928_, v_a_1929_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_stx_1927_);
return v_res_1931_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_1939_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1938_, v_a_1935_, v_a_1936_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1945_, v_a_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_1949_, v_a_1950_, v_a_1951_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_1954_, lean_object* v_b_1955_, uint8_t v_kind_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_toCold_1960_; lean_object* v_currNamespace_1961_; lean_object* v___x_1962_; lean_object* v_env_1963_; lean_object* v_nextMacroScope_1964_; lean_object* v_ngen_1965_; lean_object* v_auxDeclNGen_1966_; lean_object* v_traceState_1967_; lean_object* v_recordedDeps_1968_; lean_object* v_messages_1969_; lean_object* v_infoState_1970_; lean_object* v_snapshotTasks_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1983_; 
v_toCold_1960_ = lean_ctor_get(v___y_1957_, 0);
v_currNamespace_1961_ = lean_ctor_get(v_toCold_1960_, 4);
v___x_1962_ = lean_st_ref_take(v___y_1958_);
v_env_1963_ = lean_ctor_get(v___x_1962_, 0);
v_nextMacroScope_1964_ = lean_ctor_get(v___x_1962_, 1);
v_ngen_1965_ = lean_ctor_get(v___x_1962_, 2);
v_auxDeclNGen_1966_ = lean_ctor_get(v___x_1962_, 3);
v_traceState_1967_ = lean_ctor_get(v___x_1962_, 4);
v_recordedDeps_1968_ = lean_ctor_get(v___x_1962_, 6);
v_messages_1969_ = lean_ctor_get(v___x_1962_, 7);
v_infoState_1970_ = lean_ctor_get(v___x_1962_, 8);
v_snapshotTasks_1971_ = lean_ctor_get(v___x_1962_, 9);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v___x_1962_, 5);
lean_dec(v_unused_1984_);
v___x_1973_ = v___x_1962_;
v_isShared_1974_ = v_isSharedCheck_1983_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snapshotTasks_1971_);
lean_inc(v_infoState_1970_);
lean_inc(v_messages_1969_);
lean_inc(v_recordedDeps_1968_);
lean_inc(v_traceState_1967_);
lean_inc(v_auxDeclNGen_1966_);
lean_inc(v_ngen_1965_);
lean_inc(v_nextMacroScope_1964_);
lean_inc(v_env_1963_);
lean_dec(v___x_1962_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1983_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1975_ = lean_box(0);
lean_inc(v_currNamespace_1961_);
v___x_1976_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1963_, v_ext_1954_, v_b_1955_, v_kind_1956_, v_currNamespace_1961_);
v___x_1977_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 5, v___x_1977_);
lean_ctor_set(v___x_1973_, 0, v___x_1976_);
v___x_1979_ = v___x_1973_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_nextMacroScope_1964_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_ngen_1965_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_auxDeclNGen_1966_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v_traceState_1967_);
lean_ctor_set(v_reuseFailAlloc_1982_, 5, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1982_, 6, v_recordedDeps_1968_);
lean_ctor_set(v_reuseFailAlloc_1982_, 7, v_messages_1969_);
lean_ctor_set(v_reuseFailAlloc_1982_, 8, v_infoState_1970_);
lean_ctor_set(v_reuseFailAlloc_1982_, 9, v_snapshotTasks_1971_);
v___x_1979_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_st_ref_put(v___y_1958_, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1975_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_1985_, lean_object* v_b_1986_, lean_object* v_kind_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v_kind_boxed_1991_; lean_object* v_res_1992_; 
v_kind_boxed_1991_ = lean_unbox(v_kind_1987_);
v_res_1992_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_1985_, v_b_1986_, v_kind_boxed_1991_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_1993_, lean_object* v_00_u03b2_1994_, lean_object* v_00_u03c3_1995_, lean_object* v_ext_1996_, lean_object* v_b_1997_, uint8_t v_kind_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_1996_, v_b_1997_, v_kind_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_00_u03c3_2005_, lean_object* v_ext_2006_, lean_object* v_b_2007_, lean_object* v_kind_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v_kind_boxed_2012_; lean_object* v_res_2013_; 
v_kind_boxed_2012_ = lean_unbox(v_kind_2008_);
v_res_2013_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_2003_, v_00_u03b2_2004_, v_00_u03c3_2005_, v_ext_2006_, v_b_2007_, v_kind_boxed_2012_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_2014_, lean_object* v_declName_2015_, uint8_t v_eager_2016_, uint8_t v_attrKind_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2021_; 
lean_inc(v_declName_2015_);
v___x_2021_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_2015_, v_eager_2016_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref_known(v___x_2021_, 1);
v___x_2022_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2022_, 0, v_declName_2015_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*1, v_eager_2016_);
v___x_2023_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2014_, v___x_2022_, v_attrKind_2017_, v_a_2018_, v_a_2019_);
return v___x_2023_;
}
else
{
lean_dec(v_declName_2015_);
lean_dec_ref(v_ext_2014_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_2024_, lean_object* v_declName_2025_, lean_object* v_eager_2026_, lean_object* v_attrKind_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
uint8_t v_eager_boxed_2031_; uint8_t v_attrKind_boxed_2032_; lean_object* v_res_2033_; 
v_eager_boxed_2031_ = lean_unbox(v_eager_2026_);
v_attrKind_boxed_2032_ = lean_unbox(v_attrKind_2027_);
v_res_2033_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2024_, v_declName_2025_, v_eager_boxed_2031_, v_attrKind_boxed_2032_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_2034_, lean_object* v_declName_2035_, uint8_t v_attrKind_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v___x_2040_; 
lean_inc(v_declName_2035_);
v___x_2040_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_2035_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2048_; 
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v___x_2040_, 0);
lean_dec(v_unused_2049_);
v___x_2042_ = v___x_2040_;
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v___x_2040_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v_declName_2035_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_declName_2035_);
v___x_2045_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2034_, v___x_2045_, v_attrKind_2036_, v_a_2037_, v_a_2038_);
return v___x_2046_;
}
}
}
else
{
lean_dec(v_declName_2035_);
lean_dec_ref(v_ext_2034_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_2050_, lean_object* v_declName_2051_, lean_object* v_attrKind_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
uint8_t v_attrKind_boxed_2056_; lean_object* v_res_2057_; 
v_attrKind_boxed_2056_ = lean_unbox(v_attrKind_2052_);
v_res_2057_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2050_, v_declName_2051_, v_attrKind_boxed_2056_, v_a_2053_, v_a_2054_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_2058_, lean_object* v_declName_2059_, uint8_t v_attrKind_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_declName_2059_);
v___x_2065_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2058_, v___x_2064_, v_attrKind_2060_, v_a_2061_, v_a_2062_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_2066_, lean_object* v_declName_2067_, lean_object* v_attrKind_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
uint8_t v_attrKind_boxed_2072_; lean_object* v_res_2073_; 
v_attrKind_boxed_2072_ = lean_unbox(v_attrKind_2068_);
v_res_2073_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2066_, v_declName_2067_, v_attrKind_boxed_2072_, v_a_2069_, v_a_2070_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_2074_, lean_object* v_s_2075_){
_start:
{
lean_object* v_casesTypes_2076_; lean_object* v_funCC_2077_; lean_object* v_ematch_2078_; lean_object* v_inj_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
v_casesTypes_2076_ = lean_ctor_get(v_s_2075_, 0);
v_funCC_2077_ = lean_ctor_get(v_s_2075_, 2);
v_ematch_2078_ = lean_ctor_get(v_s_2075_, 3);
v_inj_2079_ = lean_ctor_get(v_s_2075_, 4);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_s_2075_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v_s_2075_, 1);
lean_dec(v_unused_2087_);
v___x_2081_ = v_s_2075_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_inj_2079_);
lean_inc(v_ematch_2078_);
lean_inc(v_funCC_2077_);
lean_inc(v_casesTypes_2076_);
lean_dec(v_s_2075_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v_a_2074_);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_casesTypes_2076_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_a_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_funCC_2077_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_ematch_2078_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_inj_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_2088_, lean_object* v_declName_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_ext_2095_; lean_object* v_toEnvExtension_2096_; lean_object* v_env_2097_; lean_object* v_asyncMode_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v_extThms_2101_; lean_object* v___x_2102_; 
v___x_2093_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2094_ = lean_st_ref_get(v_a_2091_);
v_ext_2095_ = lean_ctor_get(v_ext_2088_, 1);
v_toEnvExtension_2096_ = lean_ctor_get(v_ext_2095_, 0);
v_env_2097_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_ref(v_env_2097_);
lean_dec(v___x_2094_);
v_asyncMode_2098_ = lean_ctor_get(v_toEnvExtension_2096_, 2);
v___x_2099_ = 0;
v___x_2100_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2093_, v_ext_2088_, v_env_2097_, v_asyncMode_2098_, v___x_2099_);
v_extThms_2101_ = lean_ctor_get(v___x_2100_, 1);
lean_inc_ref(v_extThms_2101_);
lean_dec(v___x_2100_);
v___x_2102_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_2101_, v_declName_2089_, v_a_2090_, v_a_2091_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2133_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2133_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2133_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v_env_2109_; lean_object* v_nextMacroScope_2110_; lean_object* v_ngen_2111_; lean_object* v_auxDeclNGen_2112_; lean_object* v_traceState_2113_; lean_object* v_recordedDeps_2114_; lean_object* v_messages_2115_; lean_object* v_infoState_2116_; lean_object* v_snapshotTasks_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2131_; 
v___f_2107_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_2107_, 0, v_a_2103_);
v___x_2108_ = lean_st_ref_take(v_a_2091_);
v_env_2109_ = lean_ctor_get(v___x_2108_, 0);
v_nextMacroScope_2110_ = lean_ctor_get(v___x_2108_, 1);
v_ngen_2111_ = lean_ctor_get(v___x_2108_, 2);
v_auxDeclNGen_2112_ = lean_ctor_get(v___x_2108_, 3);
v_traceState_2113_ = lean_ctor_get(v___x_2108_, 4);
v_recordedDeps_2114_ = lean_ctor_get(v___x_2108_, 6);
v_messages_2115_ = lean_ctor_get(v___x_2108_, 7);
v_infoState_2116_ = lean_ctor_get(v___x_2108_, 8);
v_snapshotTasks_2117_ = lean_ctor_get(v___x_2108_, 9);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2108_, 5);
lean_dec(v_unused_2132_);
v___x_2119_ = v___x_2108_;
v_isShared_2120_ = v_isSharedCheck_2131_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_snapshotTasks_2117_);
lean_inc(v_infoState_2116_);
lean_inc(v_messages_2115_);
lean_inc(v_recordedDeps_2114_);
lean_inc(v_traceState_2113_);
lean_inc(v_auxDeclNGen_2112_);
lean_inc(v_ngen_2111_);
lean_inc(v_nextMacroScope_2110_);
lean_inc(v_env_2109_);
lean_dec(v___x_2108_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2131_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2088_, v_env_2109_, v___f_2107_);
v___x_2123_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 5, v___x_2123_);
lean_ctor_set(v___x_2119_, 0, v___x_2122_);
v___x_2125_ = v___x_2119_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_nextMacroScope_2110_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_ngen_2111_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_auxDeclNGen_2112_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_traceState_2113_);
lean_ctor_set(v_reuseFailAlloc_2130_, 5, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2130_, 6, v_recordedDeps_2114_);
lean_ctor_set(v_reuseFailAlloc_2130_, 7, v_messages_2115_);
lean_ctor_set(v_reuseFailAlloc_2130_, 8, v_infoState_2116_);
lean_ctor_set(v_reuseFailAlloc_2130_, 9, v_snapshotTasks_2117_);
v___x_2125_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_st_ref_put(v_a_2091_, v___x_2125_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2121_);
v___x_2128_ = v___x_2105_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2121_);
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
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_ext_2088_);
v_a_2134_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2102_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2102_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_2142_, lean_object* v_declName_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2142_, v_declName_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_2148_, lean_object* v_s_2149_){
_start:
{
lean_object* v_extThms_2150_; lean_object* v_funCC_2151_; lean_object* v_ematch_2152_; lean_object* v_inj_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_extThms_2150_ = lean_ctor_get(v_s_2149_, 1);
v_funCC_2151_ = lean_ctor_get(v_s_2149_, 2);
v_ematch_2152_ = lean_ctor_get(v_s_2149_, 3);
v_inj_2153_ = lean_ctor_get(v_s_2149_, 4);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_s_2149_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v_s_2149_, 0);
lean_dec(v_unused_2161_);
v___x_2155_ = v_s_2149_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_inj_2153_);
lean_inc(v_ematch_2152_);
lean_inc(v_funCC_2151_);
lean_inc(v_extThms_2150_);
lean_dec(v_s_2149_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v_a_2148_);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2148_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_extThms_2150_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_funCC_2151_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_ematch_2152_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_inj_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_2162_, lean_object* v_declName_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_2163_);
v___x_2168_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2169_; lean_object* v_ext_2170_; lean_object* v_toEnvExtension_2171_; lean_object* v_env_2172_; lean_object* v_asyncMode_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v_casesTypes_2176_; lean_object* v___x_2177_; 
lean_dec_ref_known(v___x_2168_, 1);
v___x_2169_ = lean_st_ref_get(v_a_2165_);
v_ext_2170_ = lean_ctor_get(v_ext_2162_, 1);
v_toEnvExtension_2171_ = lean_ctor_get(v_ext_2170_, 0);
v_env_2172_ = lean_ctor_get(v___x_2169_, 0);
lean_inc_ref(v_env_2172_);
lean_dec(v___x_2169_);
v_asyncMode_2173_ = lean_ctor_get(v_toEnvExtension_2171_, 2);
v___x_2174_ = 0;
v___x_2175_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2167_, v_ext_2162_, v_env_2172_, v_asyncMode_2173_, v___x_2174_);
v_casesTypes_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc_ref(v_casesTypes_2176_);
lean_dec(v___x_2175_);
v___x_2177_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_2176_, v_declName_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2208_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2208_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2208_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v_env_2184_; lean_object* v_nextMacroScope_2185_; lean_object* v_ngen_2186_; lean_object* v_auxDeclNGen_2187_; lean_object* v_traceState_2188_; lean_object* v_recordedDeps_2189_; lean_object* v_messages_2190_; lean_object* v_infoState_2191_; lean_object* v_snapshotTasks_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2206_; 
v___f_2182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_2182_, 0, v_a_2178_);
v___x_2183_ = lean_st_ref_take(v_a_2165_);
v_env_2184_ = lean_ctor_get(v___x_2183_, 0);
v_nextMacroScope_2185_ = lean_ctor_get(v___x_2183_, 1);
v_ngen_2186_ = lean_ctor_get(v___x_2183_, 2);
v_auxDeclNGen_2187_ = lean_ctor_get(v___x_2183_, 3);
v_traceState_2188_ = lean_ctor_get(v___x_2183_, 4);
v_recordedDeps_2189_ = lean_ctor_get(v___x_2183_, 6);
v_messages_2190_ = lean_ctor_get(v___x_2183_, 7);
v_infoState_2191_ = lean_ctor_get(v___x_2183_, 8);
v_snapshotTasks_2192_ = lean_ctor_get(v___x_2183_, 9);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2183_, 5);
lean_dec(v_unused_2207_);
v___x_2194_ = v___x_2183_;
v_isShared_2195_ = v_isSharedCheck_2206_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_snapshotTasks_2192_);
lean_inc(v_infoState_2191_);
lean_inc(v_messages_2190_);
lean_inc(v_recordedDeps_2189_);
lean_inc(v_traceState_2188_);
lean_inc(v_auxDeclNGen_2187_);
lean_inc(v_ngen_2186_);
lean_inc(v_nextMacroScope_2185_);
lean_inc(v_env_2184_);
lean_dec(v___x_2183_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2206_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2196_ = lean_box(0);
v___x_2197_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2162_, v_env_2184_, v___f_2182_);
v___x_2198_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 5, v___x_2198_);
lean_ctor_set(v___x_2194_, 0, v___x_2197_);
v___x_2200_ = v___x_2194_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_nextMacroScope_2185_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_ngen_2186_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_auxDeclNGen_2187_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_traceState_2188_);
lean_ctor_set(v_reuseFailAlloc_2205_, 5, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2205_, 6, v_recordedDeps_2189_);
lean_ctor_set(v_reuseFailAlloc_2205_, 7, v_messages_2190_);
lean_ctor_set(v_reuseFailAlloc_2205_, 8, v_infoState_2191_);
lean_ctor_set(v_reuseFailAlloc_2205_, 9, v_snapshotTasks_2192_);
v___x_2200_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = lean_st_ref_put(v_a_2165_, v___x_2200_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2196_);
v___x_2203_ = v___x_2180_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2196_);
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
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v_ext_2162_);
v_a_2209_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2177_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2177_);
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
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
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
lean_dec(v_declName_2163_);
lean_dec_ref(v_ext_2162_);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_2217_, lean_object* v_declName_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2217_, v_declName_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_2223_, lean_object* v_s_2224_){
_start:
{
lean_object* v_casesTypes_2225_; lean_object* v_extThms_2226_; lean_object* v_ematch_2227_; lean_object* v_inj_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_casesTypes_2225_ = lean_ctor_get(v_s_2224_, 0);
v_extThms_2226_ = lean_ctor_get(v_s_2224_, 1);
v_ematch_2227_ = lean_ctor_get(v_s_2224_, 3);
v_inj_2228_ = lean_ctor_get(v_s_2224_, 4);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_s_2224_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; 
v_unused_2236_ = lean_ctor_get(v_s_2224_, 2);
lean_dec(v_unused_2236_);
v___x_2230_ = v_s_2224_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_inj_2228_);
lean_inc(v_ematch_2227_);
lean_inc(v_extThms_2226_);
lean_inc(v_casesTypes_2225_);
lean_dec(v_s_2224_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 2, v___x_2223_);
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_casesTypes_2225_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_extThms_2226_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_ematch_2227_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_inj_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_2237_, lean_object* v_t_2238_){
_start:
{
if (lean_obj_tag(v_t_2238_) == 0)
{
lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v_l_2241_; lean_object* v_r_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2896_; 
v_k_2239_ = lean_ctor_get(v_t_2238_, 1);
v_v_2240_ = lean_ctor_get(v_t_2238_, 2);
v_l_2241_ = lean_ctor_get(v_t_2238_, 3);
v_r_2242_ = lean_ctor_get(v_t_2238_, 4);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_t_2238_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v_t_2238_, 0);
lean_dec(v_unused_2897_);
v___x_2244_ = v_t_2238_;
v_isShared_2245_ = v_isSharedCheck_2896_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_r_2242_);
lean_inc(v_l_2241_);
lean_inc(v_v_2240_);
lean_inc(v_k_2239_);
lean_dec(v_t_2238_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2896_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
uint8_t v___x_2246_; 
v___x_2246_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2237_, v_k_2239_);
switch(v___x_2246_)
{
case 0:
{
lean_object* v_impl_2247_; lean_object* v___x_2248_; 
v_impl_2247_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2237_, v_l_2241_);
v___x_2248_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2247_) == 0)
{
if (lean_obj_tag(v_r_2242_) == 0)
{
lean_object* v_size_2249_; lean_object* v_size_2250_; lean_object* v_k_2251_; lean_object* v_v_2252_; lean_object* v_l_2253_; lean_object* v_r_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v_size_2249_ = lean_ctor_get(v_impl_2247_, 0);
v_size_2250_ = lean_ctor_get(v_r_2242_, 0);
v_k_2251_ = lean_ctor_get(v_r_2242_, 1);
v_v_2252_ = lean_ctor_get(v_r_2242_, 2);
v_l_2253_ = lean_ctor_get(v_r_2242_, 3);
lean_inc(v_l_2253_);
v_r_2254_ = lean_ctor_get(v_r_2242_, 4);
v___x_2255_ = lean_unsigned_to_nat(3u);
v___x_2256_ = lean_nat_mul(v___x_2255_, v_size_2249_);
v___x_2257_ = lean_nat_dec_lt(v___x_2256_, v_size_2250_);
lean_dec(v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
lean_dec(v_l_2253_);
v___x_2258_ = lean_nat_add(v___x_2248_, v_size_2249_);
v___x_2259_ = lean_nat_add(v___x_2258_, v_size_2250_);
lean_dec(v___x_2258_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 3, v_impl_2247_);
lean_ctor_set(v___x_2244_, 0, v___x_2259_);
v___x_2261_ = v___x_2244_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_impl_2247_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v_r_2242_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
else
{
lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2326_; 
lean_inc(v_r_2254_);
lean_inc(v_v_2252_);
lean_inc(v_k_2251_);
lean_inc(v_size_2250_);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; lean_object* v_unused_2328_; lean_object* v_unused_2329_; lean_object* v_unused_2330_; lean_object* v_unused_2331_; 
v_unused_2327_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_r_2242_, 2);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_r_2242_, 1);
lean_dec(v_unused_2330_);
v_unused_2331_ = lean_ctor_get(v_r_2242_, 0);
lean_dec(v_unused_2331_);
v___x_2264_ = v_r_2242_;
v_isShared_2265_ = v_isSharedCheck_2326_;
goto v_resetjp_2263_;
}
else
{
lean_dec(v_r_2242_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2326_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v_size_2266_; lean_object* v_k_2267_; lean_object* v_v_2268_; lean_object* v_l_2269_; lean_object* v_r_2270_; lean_object* v_size_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_size_2266_ = lean_ctor_get(v_l_2253_, 0);
v_k_2267_ = lean_ctor_get(v_l_2253_, 1);
v_v_2268_ = lean_ctor_get(v_l_2253_, 2);
v_l_2269_ = lean_ctor_get(v_l_2253_, 3);
v_r_2270_ = lean_ctor_get(v_l_2253_, 4);
v_size_2271_ = lean_ctor_get(v_r_2254_, 0);
v___x_2272_ = lean_unsigned_to_nat(2u);
v___x_2273_ = lean_nat_mul(v___x_2272_, v_size_2271_);
v___x_2274_ = lean_nat_dec_lt(v_size_2266_, v___x_2273_);
lean_dec(v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2302_; 
lean_inc(v_r_2270_);
lean_inc(v_l_2269_);
lean_inc(v_v_2268_);
lean_inc(v_k_2267_);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_l_2253_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; lean_object* v_unused_2304_; lean_object* v_unused_2305_; lean_object* v_unused_2306_; lean_object* v_unused_2307_; 
v_unused_2303_ = lean_ctor_get(v_l_2253_, 4);
lean_dec(v_unused_2303_);
v_unused_2304_ = lean_ctor_get(v_l_2253_, 3);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_l_2253_, 2);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_l_2253_, 1);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_l_2253_, 0);
lean_dec(v_unused_2307_);
v___x_2276_ = v_l_2253_;
v_isShared_2277_ = v_isSharedCheck_2302_;
goto v_resetjp_2275_;
}
else
{
lean_dec(v_l_2253_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2302_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2292_; 
v___x_2278_ = lean_nat_add(v___x_2248_, v_size_2249_);
v___x_2279_ = lean_nat_add(v___x_2278_, v_size_2250_);
lean_dec(v_size_2250_);
if (lean_obj_tag(v_l_2269_) == 0)
{
lean_object* v_size_2300_; 
v_size_2300_ = lean_ctor_get(v_l_2269_, 0);
lean_inc(v_size_2300_);
v___y_2292_ = v_size_2300_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_unsigned_to_nat(0u);
v___y_2292_ = v___x_2301_;
goto v___jp_2291_;
}
v___jp_2280_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_nat_add(v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec(v___y_2282_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 4, v_r_2254_);
lean_ctor_set(v___x_2276_, 3, v_r_2270_);
lean_ctor_set(v___x_2276_, 2, v_v_2252_);
lean_ctor_set(v___x_2276_, 1, v_k_2251_);
lean_ctor_set(v___x_2276_, 0, v___x_2284_);
v___x_2286_ = v___x_2276_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2284_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_k_2251_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_v_2252_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_r_2270_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v_r_2254_);
v___x_2286_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 4, v___x_2286_);
lean_ctor_set(v___x_2264_, 3, v___y_2281_);
lean_ctor_set(v___x_2264_, 2, v_v_2268_);
lean_ctor_set(v___x_2264_, 1, v_k_2267_);
lean_ctor_set(v___x_2264_, 0, v___x_2279_);
v___x_2288_ = v___x_2264_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_k_2267_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_v_2268_);
lean_ctor_set(v_reuseFailAlloc_2289_, 3, v___y_2281_);
lean_ctor_set(v_reuseFailAlloc_2289_, 4, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
v___jp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = lean_nat_add(v___x_2278_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec(v___x_2278_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_l_2269_);
lean_ctor_set(v___x_2244_, 3, v_impl_2247_);
lean_ctor_set(v___x_2244_, 0, v___x_2293_);
v___x_2295_ = v___x_2244_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_impl_2247_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v_l_2269_);
v___x_2295_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_nat_add(v___x_2248_, v_size_2271_);
if (lean_obj_tag(v_r_2270_) == 0)
{
lean_object* v_size_2297_; 
v_size_2297_ = lean_ctor_get(v_r_2270_, 0);
lean_inc(v_size_2297_);
v___y_2281_ = v___x_2295_;
v___y_2282_ = v___x_2296_;
v___y_2283_ = v_size_2297_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_unsigned_to_nat(0u);
v___y_2281_ = v___x_2295_;
v___y_2282_ = v___x_2296_;
v___y_2283_ = v___x_2298_;
goto v___jp_2280_;
}
}
}
}
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_del_object(v___x_2244_);
v___x_2308_ = lean_nat_add(v___x_2248_, v_size_2249_);
v___x_2309_ = lean_nat_add(v___x_2308_, v_size_2250_);
lean_dec(v_size_2250_);
v___x_2310_ = lean_nat_add(v___x_2308_, v_size_2266_);
lean_dec(v___x_2308_);
lean_inc_ref(v_impl_2247_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 4, v_l_2253_);
lean_ctor_set(v___x_2264_, 3, v_impl_2247_);
lean_ctor_set(v___x_2264_, 2, v_v_2240_);
lean_ctor_set(v___x_2264_, 1, v_k_2239_);
lean_ctor_set(v___x_2264_, 0, v___x_2310_);
v___x_2312_ = v___x_2264_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_impl_2247_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_l_2253_);
v___x_2312_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
v_isSharedCheck_2319_ = !lean_is_exclusive(v_impl_2247_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2320_ = lean_ctor_get(v_impl_2247_, 4);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_impl_2247_, 3);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_impl_2247_, 2);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_impl_2247_, 1);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_impl_2247_, 0);
lean_dec(v_unused_2324_);
v___x_2314_ = v_impl_2247_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_dec(v_impl_2247_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v_r_2254_);
lean_ctor_set(v___x_2314_, 3, v___x_2312_);
lean_ctor_set(v___x_2314_, 2, v_v_2252_);
lean_ctor_set(v___x_2314_, 1, v_k_2251_);
lean_ctor_set(v___x_2314_, 0, v___x_2309_);
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_k_2251_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_v_2252_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_r_2254_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v_size_2332_ = lean_ctor_get(v_impl_2247_, 0);
v___x_2333_ = lean_nat_add(v___x_2248_, v_size_2332_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 3, v_impl_2247_);
lean_ctor_set(v___x_2244_, 0, v___x_2333_);
v___x_2335_ = v___x_2244_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_impl_2247_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_r_2242_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
if (lean_obj_tag(v_r_2242_) == 0)
{
lean_object* v_l_2337_; 
v_l_2337_ = lean_ctor_get(v_r_2242_, 3);
lean_inc(v_l_2337_);
if (lean_obj_tag(v_l_2337_) == 0)
{
lean_object* v_r_2338_; 
v_r_2338_ = lean_ctor_get(v_r_2242_, 4);
lean_inc(v_r_2338_);
if (lean_obj_tag(v_r_2338_) == 0)
{
lean_object* v_size_2339_; lean_object* v_k_2340_; lean_object* v_v_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2354_; 
v_size_2339_ = lean_ctor_get(v_r_2242_, 0);
v_k_2340_ = lean_ctor_get(v_r_2242_, 1);
v_v_2341_ = lean_ctor_get(v_r_2242_, 2);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; lean_object* v_unused_2356_; 
v_unused_2355_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2356_);
v___x_2343_ = v_r_2242_;
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_v_2341_);
lean_inc(v_k_2340_);
lean_inc(v_size_2339_);
lean_dec(v_r_2242_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_size_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v_size_2345_ = lean_ctor_get(v_l_2337_, 0);
v___x_2346_ = lean_nat_add(v___x_2248_, v_size_2339_);
lean_dec(v_size_2339_);
v___x_2347_ = lean_nat_add(v___x_2248_, v_size_2345_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 4, v_l_2337_);
lean_ctor_set(v___x_2343_, 3, v_impl_2247_);
lean_ctor_set(v___x_2343_, 2, v_v_2240_);
lean_ctor_set(v___x_2343_, 1, v_k_2239_);
lean_ctor_set(v___x_2343_, 0, v___x_2347_);
v___x_2349_ = v___x_2343_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_impl_2247_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v_l_2337_);
v___x_2349_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_r_2338_);
lean_ctor_set(v___x_2244_, 3, v___x_2349_);
lean_ctor_set(v___x_2244_, 2, v_v_2341_);
lean_ctor_set(v___x_2244_, 1, v_k_2340_);
lean_ctor_set(v___x_2244_, 0, v___x_2346_);
v___x_2351_ = v___x_2244_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_k_2340_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_v_2341_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2352_, 4, v_r_2338_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2381_; 
v_k_2357_ = lean_ctor_get(v_r_2242_, 1);
v_v_2358_ = lean_ctor_get(v_r_2242_, 2);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; lean_object* v_unused_2383_; lean_object* v_unused_2384_; 
v_unused_2382_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_r_2242_, 0);
lean_dec(v_unused_2384_);
v___x_2360_ = v_r_2242_;
v_isShared_2361_ = v_isSharedCheck_2381_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_v_2358_);
lean_inc(v_k_2357_);
lean_dec(v_r_2242_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2381_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_k_2362_; lean_object* v_v_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2377_; 
v_k_2362_ = lean_ctor_get(v_l_2337_, 1);
v_v_2363_ = lean_ctor_get(v_l_2337_, 2);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_l_2337_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; lean_object* v_unused_2379_; lean_object* v_unused_2380_; 
v_unused_2378_ = lean_ctor_get(v_l_2337_, 4);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_l_2337_, 3);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_l_2337_, 0);
lean_dec(v_unused_2380_);
v___x_2365_ = v_l_2337_;
v_isShared_2366_ = v_isSharedCheck_2377_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_v_2363_);
lean_inc(v_k_2362_);
lean_dec(v_l_2337_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2377_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_unsigned_to_nat(3u);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 4, v_r_2338_);
lean_ctor_set(v___x_2365_, 3, v_r_2338_);
lean_ctor_set(v___x_2365_, 2, v_v_2240_);
lean_ctor_set(v___x_2365_, 1, v_k_2239_);
lean_ctor_set(v___x_2365_, 0, v___x_2248_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_r_2338_);
lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_r_2338_);
v___x_2369_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 3, v_r_2338_);
lean_ctor_set(v___x_2360_, 0, v___x_2248_);
v___x_2371_ = v___x_2360_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_k_2357_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_v_2358_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_r_2338_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_r_2338_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2371_);
lean_ctor_set(v___x_2244_, 3, v___x_2369_);
lean_ctor_set(v___x_2244_, 2, v_v_2363_);
lean_ctor_set(v___x_2244_, 1, v_k_2362_);
lean_ctor_set(v___x_2244_, 0, v___x_2367_);
v___x_2373_ = v___x_2244_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_k_2362_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_v_2363_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2385_; 
v_r_2385_ = lean_ctor_get(v_r_2242_, 4);
lean_inc(v_r_2385_);
if (lean_obj_tag(v_r_2385_) == 0)
{
lean_object* v_k_2386_; lean_object* v_v_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2398_; 
v_k_2386_ = lean_ctor_get(v_r_2242_, 1);
v_v_2387_ = lean_ctor_get(v_r_2242_, 2);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; lean_object* v_unused_2400_; lean_object* v_unused_2401_; 
v_unused_2399_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_r_2242_, 0);
lean_dec(v_unused_2401_);
v___x_2389_ = v_r_2242_;
v_isShared_2390_ = v_isSharedCheck_2398_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_v_2387_);
lean_inc(v_k_2386_);
lean_dec(v_r_2242_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2398_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = lean_unsigned_to_nat(3u);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 4, v_l_2337_);
lean_ctor_set(v___x_2389_, 2, v_v_2240_);
lean_ctor_set(v___x_2389_, 1, v_k_2239_);
lean_ctor_set(v___x_2389_, 0, v___x_2248_);
v___x_2393_ = v___x_2389_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_l_2337_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_l_2337_);
v___x_2393_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2395_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_r_2385_);
lean_ctor_set(v___x_2244_, 3, v___x_2393_);
lean_ctor_set(v___x_2244_, 2, v_v_2387_);
lean_ctor_set(v___x_2244_, 1, v_k_2386_);
lean_ctor_set(v___x_2244_, 0, v___x_2391_);
v___x_2395_ = v___x_2244_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_k_2386_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_v_2387_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v_r_2385_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_size_2402_; lean_object* v_k_2403_; lean_object* v_v_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2415_; 
v_size_2402_ = lean_ctor_get(v_r_2242_, 0);
v_k_2403_ = lean_ctor_get(v_r_2242_, 1);
v_v_2404_ = lean_ctor_get(v_r_2242_, 2);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2416_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2417_);
v___x_2406_ = v_r_2242_;
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_v_2404_);
lean_inc(v_k_2403_);
lean_inc(v_size_2402_);
lean_dec(v_r_2242_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 3, v_r_2385_);
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_size_2402_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_r_2385_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v_r_2385_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = lean_unsigned_to_nat(2u);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2409_);
lean_ctor_set(v___x_2244_, 3, v_r_2385_);
lean_ctor_set(v___x_2244_, 0, v___x_2410_);
v___x_2412_ = v___x_2244_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_r_2385_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v___x_2409_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
else
{
lean_object* v___x_2419_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 3, v_r_2242_);
lean_ctor_set(v___x_2244_, 0, v___x_2248_);
v___x_2419_ = v___x_2244_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_r_2242_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v_r_2242_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2244_);
lean_dec(v_v_2240_);
lean_dec(v_k_2239_);
if (lean_obj_tag(v_l_2241_) == 0)
{
if (lean_obj_tag(v_r_2242_) == 0)
{
lean_object* v_size_2421_; lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v_l_2424_; lean_object* v_r_2425_; lean_object* v_size_2426_; lean_object* v_k_2427_; lean_object* v_v_2428_; lean_object* v_l_2429_; lean_object* v_r_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v_size_2421_ = lean_ctor_get(v_l_2241_, 0);
v_k_2422_ = lean_ctor_get(v_l_2241_, 1);
v_v_2423_ = lean_ctor_get(v_l_2241_, 2);
v_l_2424_ = lean_ctor_get(v_l_2241_, 3);
v_r_2425_ = lean_ctor_get(v_l_2241_, 4);
lean_inc(v_r_2425_);
v_size_2426_ = lean_ctor_get(v_r_2242_, 0);
v_k_2427_ = lean_ctor_get(v_r_2242_, 1);
v_v_2428_ = lean_ctor_get(v_r_2242_, 2);
v_l_2429_ = lean_ctor_get(v_r_2242_, 3);
lean_inc(v_l_2429_);
v_r_2430_ = lean_ctor_get(v_r_2242_, 4);
v___x_2431_ = lean_unsigned_to_nat(1u);
v___x_2432_ = lean_nat_dec_lt(v_size_2421_, v_size_2426_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2568_; 
lean_inc(v_l_2424_);
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; lean_object* v_unused_2570_; lean_object* v_unused_2571_; lean_object* v_unused_2572_; lean_object* v_unused_2573_; 
v_unused_2569_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2569_);
v_unused_2570_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2570_);
v_unused_2571_ = lean_ctor_get(v_l_2241_, 2);
lean_dec(v_unused_2571_);
v_unused_2572_ = lean_ctor_get(v_l_2241_, 1);
lean_dec(v_unused_2572_);
v_unused_2573_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2573_);
v___x_2434_ = v_l_2241_;
v_isShared_2435_ = v_isSharedCheck_2568_;
goto v_resetjp_2433_;
}
else
{
lean_dec(v_l_2241_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2568_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v_tree_2437_; 
v___x_2436_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2422_, v_v_2423_, v_l_2424_, v_r_2425_);
v_tree_2437_ = lean_ctor_get(v___x_2436_, 2);
if (lean_obj_tag(v_tree_2437_) == 0)
{
lean_object* v_k_2438_; lean_object* v_v_2439_; lean_object* v_size_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
lean_inc_ref(v_tree_2437_);
v_k_2438_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_k_2438_);
v_v_2439_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_v_2439_);
lean_dec_ref(v___x_2436_);
v_size_2440_ = lean_ctor_get(v_tree_2437_, 0);
v___x_2441_ = lean_unsigned_to_nat(3u);
v___x_2442_ = lean_nat_mul(v___x_2441_, v_size_2440_);
v___x_2443_ = lean_nat_dec_lt(v___x_2442_, v_size_2426_);
lean_dec(v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_dec(v_l_2429_);
v___x_2444_ = lean_nat_add(v___x_2431_, v_size_2440_);
v___x_2445_ = lean_nat_add(v___x_2444_, v_size_2426_);
lean_dec(v___x_2444_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v_r_2242_);
lean_ctor_set(v___x_2434_, 3, v_tree_2437_);
lean_ctor_set(v___x_2434_, 2, v_v_2439_);
lean_ctor_set(v___x_2434_, 1, v_k_2438_);
lean_ctor_set(v___x_2434_, 0, v___x_2445_);
v___x_2447_ = v___x_2434_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_k_2438_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_v_2439_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_tree_2437_);
lean_ctor_set(v_reuseFailAlloc_2448_, 4, v_r_2242_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
else
{
lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2503_; 
lean_inc(v_r_2430_);
lean_inc(v_v_2428_);
lean_inc(v_k_2427_);
lean_inc(v_size_2426_);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; 
v_unused_2504_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_r_2242_, 2);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_r_2242_, 1);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_r_2242_, 0);
lean_dec(v_unused_2508_);
v___x_2450_ = v_r_2242_;
v_isShared_2451_ = v_isSharedCheck_2503_;
goto v_resetjp_2449_;
}
else
{
lean_dec(v_r_2242_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2503_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_size_2452_; lean_object* v_k_2453_; lean_object* v_v_2454_; lean_object* v_l_2455_; lean_object* v_r_2456_; lean_object* v_size_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_size_2452_ = lean_ctor_get(v_l_2429_, 0);
v_k_2453_ = lean_ctor_get(v_l_2429_, 1);
v_v_2454_ = lean_ctor_get(v_l_2429_, 2);
v_l_2455_ = lean_ctor_get(v_l_2429_, 3);
v_r_2456_ = lean_ctor_get(v_l_2429_, 4);
v_size_2457_ = lean_ctor_get(v_r_2430_, 0);
v___x_2458_ = lean_unsigned_to_nat(2u);
v___x_2459_ = lean_nat_mul(v___x_2458_, v_size_2457_);
v___x_2460_ = lean_nat_dec_lt(v_size_2452_, v___x_2459_);
lean_dec(v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2488_; 
lean_inc(v_r_2456_);
lean_inc(v_l_2455_);
lean_inc(v_v_2454_);
lean_inc(v_k_2453_);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_l_2429_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; lean_object* v_unused_2490_; lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; 
v_unused_2489_ = lean_ctor_get(v_l_2429_, 4);
lean_dec(v_unused_2489_);
v_unused_2490_ = lean_ctor_get(v_l_2429_, 3);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_l_2429_, 2);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_l_2429_, 1);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_l_2429_, 0);
lean_dec(v_unused_2493_);
v___x_2462_ = v_l_2429_;
v_isShared_2463_ = v_isSharedCheck_2488_;
goto v_resetjp_2461_;
}
else
{
lean_dec(v_l_2429_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2488_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2478_; 
v___x_2464_ = lean_nat_add(v___x_2431_, v_size_2440_);
v___x_2465_ = lean_nat_add(v___x_2464_, v_size_2426_);
lean_dec(v_size_2426_);
if (lean_obj_tag(v_l_2455_) == 0)
{
lean_object* v_size_2486_; 
v_size_2486_ = lean_ctor_get(v_l_2455_, 0);
lean_inc(v_size_2486_);
v___y_2478_ = v_size_2486_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_unsigned_to_nat(0u);
v___y_2478_ = v___x_2487_;
goto v___jp_2477_;
}
v___jp_2466_:
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2470_ = lean_nat_add(v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec(v___y_2468_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v_r_2430_);
lean_ctor_set(v___x_2462_, 3, v_r_2456_);
lean_ctor_set(v___x_2462_, 2, v_v_2428_);
lean_ctor_set(v___x_2462_, 1, v_k_2427_);
lean_ctor_set(v___x_2462_, 0, v___x_2470_);
v___x_2472_ = v___x_2462_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_r_2456_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_r_2430_);
v___x_2472_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 4, v___x_2472_);
lean_ctor_set(v___x_2450_, 3, v___y_2467_);
lean_ctor_set(v___x_2450_, 2, v_v_2454_);
lean_ctor_set(v___x_2450_, 1, v_k_2453_);
lean_ctor_set(v___x_2450_, 0, v___x_2465_);
v___x_2474_ = v___x_2450_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_k_2453_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_v_2454_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v___y_2467_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
v___jp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_nat_add(v___x_2464_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec(v___x_2464_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v_l_2455_);
lean_ctor_set(v___x_2434_, 3, v_tree_2437_);
lean_ctor_set(v___x_2434_, 2, v_v_2439_);
lean_ctor_set(v___x_2434_, 1, v_k_2438_);
lean_ctor_set(v___x_2434_, 0, v___x_2479_);
v___x_2481_ = v___x_2434_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2479_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_k_2438_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_v_2439_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_tree_2437_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_l_2455_);
v___x_2481_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_nat_add(v___x_2431_, v_size_2457_);
if (lean_obj_tag(v_r_2456_) == 0)
{
lean_object* v_size_2483_; 
v_size_2483_ = lean_ctor_get(v_r_2456_, 0);
lean_inc(v_size_2483_);
v___y_2467_ = v___x_2481_;
v___y_2468_ = v___x_2482_;
v___y_2469_ = v_size_2483_;
goto v___jp_2466_;
}
else
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_unsigned_to_nat(0u);
v___y_2467_ = v___x_2481_;
v___y_2468_ = v___x_2482_;
v___y_2469_ = v___x_2484_;
goto v___jp_2466_;
}
}
}
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2494_ = lean_nat_add(v___x_2431_, v_size_2440_);
v___x_2495_ = lean_nat_add(v___x_2494_, v_size_2426_);
lean_dec(v_size_2426_);
v___x_2496_ = lean_nat_add(v___x_2494_, v_size_2452_);
lean_dec(v___x_2494_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 4, v_l_2429_);
lean_ctor_set(v___x_2450_, 3, v_tree_2437_);
lean_ctor_set(v___x_2450_, 2, v_v_2439_);
lean_ctor_set(v___x_2450_, 1, v_k_2438_);
lean_ctor_set(v___x_2450_, 0, v___x_2496_);
v___x_2498_ = v___x_2450_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_k_2438_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_v_2439_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_tree_2437_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_l_2429_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2500_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v_r_2430_);
lean_ctor_set(v___x_2434_, 3, v___x_2498_);
lean_ctor_set(v___x_2434_, 2, v_v_2428_);
lean_ctor_set(v___x_2434_, 1, v_k_2427_);
lean_ctor_set(v___x_2434_, 0, v___x_2495_);
v___x_2500_ = v___x_2434_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_r_2430_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
}
else
{
lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2562_; 
lean_inc(v_r_2430_);
lean_inc(v_v_2428_);
lean_inc(v_k_2427_);
lean_inc(v_size_2426_);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; lean_object* v_unused_2564_; lean_object* v_unused_2565_; lean_object* v_unused_2566_; lean_object* v_unused_2567_; 
v_unused_2563_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_r_2242_, 2);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_r_2242_, 1);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_r_2242_, 0);
lean_dec(v_unused_2567_);
v___x_2510_ = v_r_2242_;
v_isShared_2511_ = v_isSharedCheck_2562_;
goto v_resetjp_2509_;
}
else
{
lean_dec(v_r_2242_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2562_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
if (lean_obj_tag(v_l_2429_) == 0)
{
if (lean_obj_tag(v_r_2430_) == 0)
{
lean_object* v_k_2512_; lean_object* v_v_2513_; lean_object* v_size_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
lean_inc(v_tree_2437_);
v_k_2512_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_k_2512_);
v_v_2513_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_v_2513_);
lean_dec_ref(v___x_2436_);
v_size_2514_ = lean_ctor_get(v_l_2429_, 0);
v___x_2515_ = lean_nat_add(v___x_2431_, v_size_2426_);
lean_dec(v_size_2426_);
v___x_2516_ = lean_nat_add(v___x_2431_, v_size_2514_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 4, v_l_2429_);
lean_ctor_set(v___x_2510_, 3, v_tree_2437_);
lean_ctor_set(v___x_2510_, 2, v_v_2513_);
lean_ctor_set(v___x_2510_, 1, v_k_2512_);
lean_ctor_set(v___x_2510_, 0, v___x_2516_);
v___x_2518_ = v___x_2510_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2513_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_tree_2437_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_l_2429_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v_r_2430_);
lean_ctor_set(v___x_2434_, 3, v___x_2518_);
lean_ctor_set(v___x_2434_, 2, v_v_2428_);
lean_ctor_set(v___x_2434_, 1, v_k_2427_);
lean_ctor_set(v___x_2434_, 0, v___x_2515_);
v___x_2520_ = v___x_2434_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_r_2430_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
else
{
lean_object* v_k_2523_; lean_object* v_v_2524_; lean_object* v_k_2525_; lean_object* v_v_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_size_2426_);
v_k_2523_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_k_2523_);
v_v_2524_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_v_2524_);
lean_dec_ref(v___x_2436_);
v_k_2525_ = lean_ctor_get(v_l_2429_, 1);
v_v_2526_ = lean_ctor_get(v_l_2429_, 2);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_l_2429_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; 
v_unused_2541_ = lean_ctor_get(v_l_2429_, 4);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_l_2429_, 3);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_l_2429_, 0);
lean_dec(v_unused_2543_);
v___x_2528_ = v_l_2429_;
v_isShared_2529_ = v_isSharedCheck_2540_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_v_2526_);
lean_inc(v_k_2525_);
lean_dec(v_l_2429_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2540_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_unsigned_to_nat(3u);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 4, v_r_2430_);
lean_ctor_set(v___x_2528_, 3, v_r_2430_);
lean_ctor_set(v___x_2528_, 2, v_v_2524_);
lean_ctor_set(v___x_2528_, 1, v_k_2523_);
lean_ctor_set(v___x_2528_, 0, v___x_2431_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2523_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2524_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_r_2430_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_r_2430_);
v___x_2532_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2534_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 3, v_r_2430_);
lean_ctor_set(v___x_2510_, 0, v___x_2431_);
v___x_2534_ = v___x_2510_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v_r_2430_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v_r_2430_);
v___x_2534_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v___x_2534_);
lean_ctor_set(v___x_2434_, 3, v___x_2532_);
lean_ctor_set(v___x_2434_, 2, v_v_2526_);
lean_ctor_set(v___x_2434_, 1, v_k_2525_);
lean_ctor_set(v___x_2434_, 0, v___x_2530_);
v___x_2536_ = v___x_2434_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_k_2525_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_v_2526_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v___x_2534_);
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
}
}
else
{
if (lean_obj_tag(v_r_2430_) == 0)
{
lean_object* v_k_2544_; lean_object* v_v_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
lean_dec(v_size_2426_);
v_k_2544_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_k_2544_);
v_v_2545_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_v_2545_);
lean_dec_ref(v___x_2436_);
v___x_2546_ = lean_unsigned_to_nat(3u);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 4, v_l_2429_);
lean_ctor_set(v___x_2510_, 2, v_v_2545_);
lean_ctor_set(v___x_2510_, 1, v_k_2544_);
lean_ctor_set(v___x_2510_, 0, v___x_2431_);
v___x_2548_ = v___x_2510_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_k_2544_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_v_2545_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_l_2429_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_l_2429_);
v___x_2548_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2550_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v_r_2430_);
lean_ctor_set(v___x_2434_, 3, v___x_2548_);
lean_ctor_set(v___x_2434_, 2, v_v_2428_);
lean_ctor_set(v___x_2434_, 1, v_k_2427_);
lean_ctor_set(v___x_2434_, 0, v___x_2546_);
v___x_2550_ = v___x_2434_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_r_2430_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v_k_2553_; lean_object* v_v_2554_; lean_object* v___x_2556_; 
v_k_2553_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_k_2553_);
v_v_2554_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_v_2554_);
lean_dec_ref(v___x_2436_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 3, v_r_2430_);
v___x_2556_ = v___x_2510_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_size_2426_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_r_2430_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_r_2430_);
v___x_2556_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_unsigned_to_nat(2u);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v___x_2556_);
lean_ctor_set(v___x_2434_, 3, v_r_2430_);
lean_ctor_set(v___x_2434_, 2, v_v_2554_);
lean_ctor_set(v___x_2434_, 1, v_k_2553_);
lean_ctor_set(v___x_2434_, 0, v___x_2557_);
v___x_2559_ = v___x_2434_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_k_2553_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_v_2554_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v_r_2430_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v___x_2556_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
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
lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2726_; 
lean_inc(v_r_2430_);
lean_inc(v_v_2428_);
lean_inc(v_k_2427_);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_r_2242_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; lean_object* v_unused_2731_; 
v_unused_2727_ = lean_ctor_get(v_r_2242_, 4);
lean_dec(v_unused_2727_);
v_unused_2728_ = lean_ctor_get(v_r_2242_, 3);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_r_2242_, 2);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_r_2242_, 1);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_r_2242_, 0);
lean_dec(v_unused_2731_);
v___x_2575_ = v_r_2242_;
v_isShared_2576_ = v_isSharedCheck_2726_;
goto v_resetjp_2574_;
}
else
{
lean_dec(v_r_2242_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2726_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v_tree_2578_; 
v___x_2577_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2427_, v_v_2428_, v_l_2429_, v_r_2430_);
v_tree_2578_ = lean_ctor_get(v___x_2577_, 2);
lean_inc(v_tree_2578_);
if (lean_obj_tag(v_tree_2578_) == 0)
{
lean_object* v_k_2579_; lean_object* v_v_2580_; lean_object* v_size_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_k_2579_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_k_2579_);
v_v_2580_ = lean_ctor_get(v___x_2577_, 1);
lean_inc(v_v_2580_);
lean_dec_ref(v___x_2577_);
v_size_2581_ = lean_ctor_get(v_tree_2578_, 0);
v___x_2582_ = lean_unsigned_to_nat(3u);
v___x_2583_ = lean_nat_mul(v___x_2582_, v_size_2581_);
v___x_2584_ = lean_nat_dec_lt(v___x_2583_, v_size_2421_);
lean_dec(v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_dec(v_r_2425_);
v___x_2585_ = lean_nat_add(v___x_2431_, v_size_2421_);
v___x_2586_ = lean_nat_add(v___x_2585_, v_size_2581_);
lean_dec(v___x_2585_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_tree_2578_);
lean_ctor_set(v___x_2575_, 3, v_l_2241_);
lean_ctor_set(v___x_2575_, 2, v_v_2580_);
lean_ctor_set(v___x_2575_, 1, v_k_2579_);
lean_ctor_set(v___x_2575_, 0, v___x_2586_);
v___x_2588_ = v___x_2575_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_k_2579_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_v_2580_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_tree_2578_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
else
{
lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2655_; 
lean_inc(v_l_2424_);
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
lean_inc(v_size_2421_);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; lean_object* v_unused_2657_; lean_object* v_unused_2658_; lean_object* v_unused_2659_; lean_object* v_unused_2660_; 
v_unused_2656_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2656_);
v_unused_2657_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_l_2241_, 2);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_l_2241_, 1);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2660_);
v___x_2591_ = v_l_2241_;
v_isShared_2592_ = v_isSharedCheck_2655_;
goto v_resetjp_2590_;
}
else
{
lean_dec(v_l_2241_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2655_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_size_2593_; lean_object* v_size_2594_; lean_object* v_k_2595_; lean_object* v_v_2596_; lean_object* v_l_2597_; lean_object* v_r_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_size_2593_ = lean_ctor_get(v_l_2424_, 0);
v_size_2594_ = lean_ctor_get(v_r_2425_, 0);
v_k_2595_ = lean_ctor_get(v_r_2425_, 1);
v_v_2596_ = lean_ctor_get(v_r_2425_, 2);
v_l_2597_ = lean_ctor_get(v_r_2425_, 3);
v_r_2598_ = lean_ctor_get(v_r_2425_, 4);
v___x_2599_ = lean_unsigned_to_nat(2u);
v___x_2600_ = lean_nat_mul(v___x_2599_, v_size_2593_);
v___x_2601_ = lean_nat_dec_lt(v_size_2594_, v___x_2600_);
lean_dec(v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2639_; 
lean_inc(v_r_2598_);
lean_inc(v_l_2597_);
lean_inc(v_v_2596_);
lean_inc(v_k_2595_);
lean_del_object(v___x_2591_);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_r_2425_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; lean_object* v_unused_2641_; lean_object* v_unused_2642_; lean_object* v_unused_2643_; lean_object* v_unused_2644_; 
v_unused_2640_ = lean_ctor_get(v_r_2425_, 4);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_r_2425_, 3);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v_r_2425_, 2);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_r_2425_, 1);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_r_2425_, 0);
lean_dec(v_unused_2644_);
v___x_2603_ = v_r_2425_;
v_isShared_2604_ = v_isSharedCheck_2639_;
goto v_resetjp_2602_;
}
else
{
lean_dec(v_r_2425_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2639_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___x_2627_; lean_object* v___y_2629_; 
v___x_2605_ = lean_nat_add(v___x_2431_, v_size_2421_);
lean_dec(v_size_2421_);
v___x_2606_ = lean_nat_add(v___x_2605_, v_size_2581_);
lean_dec(v___x_2605_);
v___x_2627_ = lean_nat_add(v___x_2431_, v_size_2593_);
if (lean_obj_tag(v_l_2597_) == 0)
{
lean_object* v_size_2637_; 
v_size_2637_ = lean_ctor_get(v_l_2597_, 0);
lean_inc(v_size_2637_);
v___y_2629_ = v_size_2637_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v___y_2629_ = v___x_2638_;
goto v___jp_2628_;
}
v___jp_2607_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_nat_add(v___y_2608_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec(v___y_2608_);
lean_inc_ref(v_tree_2578_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 4, v_tree_2578_);
lean_ctor_set(v___x_2603_, 3, v_r_2598_);
lean_ctor_set(v___x_2603_, 2, v_v_2580_);
lean_ctor_set(v___x_2603_, 1, v_k_2579_);
lean_ctor_set(v___x_2603_, 0, v___x_2611_);
v___x_2613_ = v___x_2603_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_k_2579_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_v_2580_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_r_2598_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_tree_2578_);
v___x_2613_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
v_isSharedCheck_2620_ = !lean_is_exclusive(v_tree_2578_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; lean_object* v_unused_2622_; lean_object* v_unused_2623_; lean_object* v_unused_2624_; lean_object* v_unused_2625_; 
v_unused_2621_ = lean_ctor_get(v_tree_2578_, 4);
lean_dec(v_unused_2621_);
v_unused_2622_ = lean_ctor_get(v_tree_2578_, 3);
lean_dec(v_unused_2622_);
v_unused_2623_ = lean_ctor_get(v_tree_2578_, 2);
lean_dec(v_unused_2623_);
v_unused_2624_ = lean_ctor_get(v_tree_2578_, 1);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_tree_2578_, 0);
lean_dec(v_unused_2625_);
v___x_2615_ = v_tree_2578_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_dec(v_tree_2578_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 4, v___x_2613_);
lean_ctor_set(v___x_2615_, 3, v___y_2609_);
lean_ctor_set(v___x_2615_, 2, v_v_2596_);
lean_ctor_set(v___x_2615_, 1, v_k_2595_);
lean_ctor_set(v___x_2615_, 0, v___x_2606_);
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_k_2595_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_v_2596_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v___y_2609_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v___x_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2630_ = lean_nat_add(v___x_2627_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec(v___x_2627_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_l_2597_);
lean_ctor_set(v___x_2575_, 3, v_l_2424_);
lean_ctor_set(v___x_2575_, 2, v_v_2423_);
lean_ctor_set(v___x_2575_, 1, v_k_2422_);
lean_ctor_set(v___x_2575_, 0, v___x_2630_);
v___x_2632_ = v___x_2575_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_l_2597_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_nat_add(v___x_2431_, v_size_2581_);
if (lean_obj_tag(v_r_2598_) == 0)
{
lean_object* v_size_2634_; 
v_size_2634_ = lean_ctor_get(v_r_2598_, 0);
lean_inc(v_size_2634_);
v___y_2608_ = v___x_2633_;
v___y_2609_ = v___x_2632_;
v___y_2610_ = v_size_2634_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_unsigned_to_nat(0u);
v___y_2608_ = v___x_2633_;
v___y_2609_ = v___x_2632_;
v___y_2610_ = v___x_2635_;
goto v___jp_2607_;
}
}
}
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2645_ = lean_nat_add(v___x_2431_, v_size_2421_);
lean_dec(v_size_2421_);
v___x_2646_ = lean_nat_add(v___x_2645_, v_size_2581_);
lean_dec(v___x_2645_);
v___x_2647_ = lean_nat_add(v___x_2431_, v_size_2581_);
v___x_2648_ = lean_nat_add(v___x_2647_, v_size_2594_);
lean_dec(v___x_2647_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_tree_2578_);
lean_ctor_set(v___x_2575_, 3, v_r_2425_);
lean_ctor_set(v___x_2575_, 2, v_v_2580_);
lean_ctor_set(v___x_2575_, 1, v_k_2579_);
lean_ctor_set(v___x_2575_, 0, v___x_2648_);
v___x_2650_ = v___x_2575_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_k_2579_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_v_2580_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_r_2425_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_tree_2578_);
v___x_2650_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___x_2650_);
lean_ctor_set(v___x_2591_, 0, v___x_2646_);
v___x_2652_ = v___x_2591_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2424_) == 0)
{
lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2684_; 
lean_inc_ref(v_l_2424_);
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
lean_inc(v_size_2421_);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; lean_object* v_unused_2689_; 
v_unused_2685_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_l_2241_, 2);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_l_2241_, 1);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2689_);
v___x_2662_ = v_l_2241_;
v_isShared_2663_ = v_isSharedCheck_2684_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v_l_2241_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2684_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
if (lean_obj_tag(v_r_2425_) == 0)
{
lean_object* v_k_2664_; lean_object* v_v_2665_; lean_object* v_size_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v_k_2664_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_k_2664_);
v_v_2665_ = lean_ctor_get(v___x_2577_, 1);
lean_inc(v_v_2665_);
lean_dec_ref(v___x_2577_);
v_size_2666_ = lean_ctor_get(v_r_2425_, 0);
v___x_2667_ = lean_nat_add(v___x_2431_, v_size_2421_);
lean_dec(v_size_2421_);
v___x_2668_ = lean_nat_add(v___x_2431_, v_size_2666_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_tree_2578_);
lean_ctor_set(v___x_2575_, 3, v_r_2425_);
lean_ctor_set(v___x_2575_, 2, v_v_2665_);
lean_ctor_set(v___x_2575_, 1, v_k_2664_);
lean_ctor_set(v___x_2575_, 0, v___x_2668_);
v___x_2670_ = v___x_2575_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_k_2664_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_v_2665_);
lean_ctor_set(v_reuseFailAlloc_2674_, 3, v_r_2425_);
lean_ctor_set(v_reuseFailAlloc_2674_, 4, v_tree_2578_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 4, v___x_2670_);
lean_ctor_set(v___x_2662_, 0, v___x_2667_);
v___x_2672_ = v___x_2662_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_object* v_k_2675_; lean_object* v_v_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
lean_dec(v_size_2421_);
v_k_2675_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_k_2675_);
v_v_2676_ = lean_ctor_get(v___x_2577_, 1);
lean_inc(v_v_2676_);
lean_dec_ref(v___x_2577_);
v___x_2677_ = lean_unsigned_to_nat(3u);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_r_2425_);
lean_ctor_set(v___x_2575_, 3, v_r_2425_);
lean_ctor_set(v___x_2575_, 2, v_v_2676_);
lean_ctor_set(v___x_2575_, 1, v_k_2675_);
lean_ctor_set(v___x_2575_, 0, v___x_2431_);
v___x_2679_ = v___x_2575_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2675_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2676_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_r_2425_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_r_2425_);
v___x_2679_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 4, v___x_2679_);
lean_ctor_set(v___x_2662_, 0, v___x_2677_);
v___x_2681_ = v___x_2662_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v___x_2679_);
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
else
{
if (lean_obj_tag(v_r_2425_) == 0)
{
lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2714_; 
lean_inc(v_l_2424_);
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2714_ == 0)
{
lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2715_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_l_2241_, 2);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_l_2241_, 1);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2719_);
v___x_2691_ = v_l_2241_;
v_isShared_2692_ = v_isSharedCheck_2714_;
goto v_resetjp_2690_;
}
else
{
lean_dec(v_l_2241_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2714_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v_k_2693_; lean_object* v_v_2694_; lean_object* v_k_2695_; lean_object* v_v_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2710_; 
v_k_2693_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_k_2693_);
v_v_2694_ = lean_ctor_get(v___x_2577_, 1);
lean_inc(v_v_2694_);
lean_dec_ref(v___x_2577_);
v_k_2695_ = lean_ctor_get(v_r_2425_, 1);
v_v_2696_ = lean_ctor_get(v_r_2425_, 2);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_r_2425_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2711_ = lean_ctor_get(v_r_2425_, 4);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_r_2425_, 3);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_r_2425_, 0);
lean_dec(v_unused_2713_);
v___x_2698_ = v_r_2425_;
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_v_2696_);
lean_inc(v_k_2695_);
lean_dec(v_r_2425_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = lean_unsigned_to_nat(3u);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 4, v_l_2424_);
lean_ctor_set(v___x_2698_, 3, v_l_2424_);
lean_ctor_set(v___x_2698_, 2, v_v_2423_);
lean_ctor_set(v___x_2698_, 1, v_k_2422_);
lean_ctor_set(v___x_2698_, 0, v___x_2431_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_l_2424_);
v___x_2702_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_l_2424_);
lean_ctor_set(v___x_2575_, 3, v_l_2424_);
lean_ctor_set(v___x_2575_, 2, v_v_2694_);
lean_ctor_set(v___x_2575_, 1, v_k_2693_);
lean_ctor_set(v___x_2575_, 0, v___x_2431_);
v___x_2704_ = v___x_2575_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_k_2693_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_v_2694_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_l_2424_);
v___x_2704_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 4, v___x_2704_);
lean_ctor_set(v___x_2691_, 3, v___x_2702_);
lean_ctor_set(v___x_2691_, 2, v_v_2696_);
lean_ctor_set(v___x_2691_, 1, v_k_2695_);
lean_ctor_set(v___x_2691_, 0, v___x_2700_);
v___x_2706_ = v___x_2691_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_k_2695_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_v_2696_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
else
{
lean_object* v_k_2720_; lean_object* v_v_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v_k_2720_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_k_2720_);
v_v_2721_ = lean_ctor_get(v___x_2577_, 1);
lean_inc(v_v_2721_);
lean_dec_ref(v___x_2577_);
v___x_2722_ = lean_unsigned_to_nat(2u);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_r_2425_);
lean_ctor_set(v___x_2575_, 3, v_l_2241_);
lean_ctor_set(v___x_2575_, 2, v_v_2721_);
lean_ctor_set(v___x_2575_, 1, v_k_2720_);
lean_ctor_set(v___x_2575_, 0, v___x_2722_);
v___x_2724_ = v___x_2575_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_r_2425_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
else
{
return v_l_2241_;
}
}
else
{
return v_r_2242_;
}
}
default: 
{
lean_object* v_impl_2732_; lean_object* v___x_2733_; 
v_impl_2732_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2237_, v_r_2242_);
v___x_2733_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2732_) == 0)
{
if (lean_obj_tag(v_l_2241_) == 0)
{
lean_object* v_size_2734_; lean_object* v_size_2735_; lean_object* v_k_2736_; lean_object* v_v_2737_; lean_object* v_l_2738_; lean_object* v_r_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_size_2734_ = lean_ctor_get(v_impl_2732_, 0);
v_size_2735_ = lean_ctor_get(v_l_2241_, 0);
v_k_2736_ = lean_ctor_get(v_l_2241_, 1);
v_v_2737_ = lean_ctor_get(v_l_2241_, 2);
v_l_2738_ = lean_ctor_get(v_l_2241_, 3);
v_r_2739_ = lean_ctor_get(v_l_2241_, 4);
lean_inc(v_r_2739_);
v___x_2740_ = lean_unsigned_to_nat(3u);
v___x_2741_ = lean_nat_mul(v___x_2740_, v_size_2734_);
v___x_2742_ = lean_nat_dec_lt(v___x_2741_, v_size_2735_);
lean_dec(v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
lean_dec(v_r_2739_);
v___x_2743_ = lean_nat_add(v___x_2733_, v_size_2735_);
v___x_2744_ = lean_nat_add(v___x_2743_, v_size_2734_);
lean_dec(v___x_2743_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_impl_2732_);
lean_ctor_set(v___x_2244_, 0, v___x_2744_);
v___x_2746_ = v___x_2244_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_impl_2732_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
else
{
lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2813_; 
lean_inc(v_l_2738_);
lean_inc(v_v_2737_);
lean_inc(v_k_2736_);
lean_inc(v_size_2735_);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; lean_object* v_unused_2815_; lean_object* v_unused_2816_; lean_object* v_unused_2817_; lean_object* v_unused_2818_; 
v_unused_2814_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2814_);
v_unused_2815_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2815_);
v_unused_2816_ = lean_ctor_get(v_l_2241_, 2);
lean_dec(v_unused_2816_);
v_unused_2817_ = lean_ctor_get(v_l_2241_, 1);
lean_dec(v_unused_2817_);
v_unused_2818_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2818_);
v___x_2749_ = v_l_2241_;
v_isShared_2750_ = v_isSharedCheck_2813_;
goto v_resetjp_2748_;
}
else
{
lean_dec(v_l_2241_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2813_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_size_2751_; lean_object* v_size_2752_; lean_object* v_k_2753_; lean_object* v_v_2754_; lean_object* v_l_2755_; lean_object* v_r_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_size_2751_ = lean_ctor_get(v_l_2738_, 0);
v_size_2752_ = lean_ctor_get(v_r_2739_, 0);
v_k_2753_ = lean_ctor_get(v_r_2739_, 1);
v_v_2754_ = lean_ctor_get(v_r_2739_, 2);
v_l_2755_ = lean_ctor_get(v_r_2739_, 3);
v_r_2756_ = lean_ctor_get(v_r_2739_, 4);
v___x_2757_ = lean_unsigned_to_nat(2u);
v___x_2758_ = lean_nat_mul(v___x_2757_, v_size_2751_);
v___x_2759_ = lean_nat_dec_lt(v_size_2752_, v___x_2758_);
lean_dec(v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2788_; 
lean_inc(v_r_2756_);
lean_inc(v_l_2755_);
lean_inc(v_v_2754_);
lean_inc(v_k_2753_);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_r_2739_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; lean_object* v_unused_2790_; lean_object* v_unused_2791_; lean_object* v_unused_2792_; lean_object* v_unused_2793_; 
v_unused_2789_ = lean_ctor_get(v_r_2739_, 4);
lean_dec(v_unused_2789_);
v_unused_2790_ = lean_ctor_get(v_r_2739_, 3);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_r_2739_, 2);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_r_2739_, 1);
lean_dec(v_unused_2792_);
v_unused_2793_ = lean_ctor_get(v_r_2739_, 0);
lean_dec(v_unused_2793_);
v___x_2761_ = v_r_2739_;
v_isShared_2762_ = v_isSharedCheck_2788_;
goto v_resetjp_2760_;
}
else
{
lean_dec(v_r_2739_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2788_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___x_2776_; lean_object* v___y_2778_; 
v___x_2763_ = lean_nat_add(v___x_2733_, v_size_2735_);
lean_dec(v_size_2735_);
v___x_2764_ = lean_nat_add(v___x_2763_, v_size_2734_);
lean_dec(v___x_2763_);
v___x_2776_ = lean_nat_add(v___x_2733_, v_size_2751_);
if (lean_obj_tag(v_l_2755_) == 0)
{
lean_object* v_size_2786_; 
v_size_2786_ = lean_ctor_get(v_l_2755_, 0);
lean_inc(v_size_2786_);
v___y_2778_ = v_size_2786_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_unsigned_to_nat(0u);
v___y_2778_ = v___x_2787_;
goto v___jp_2777_;
}
v___jp_2765_:
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = lean_nat_add(v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec(v___y_2767_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 4, v_impl_2732_);
lean_ctor_set(v___x_2761_, 3, v_r_2756_);
lean_ctor_set(v___x_2761_, 2, v_v_2240_);
lean_ctor_set(v___x_2761_, 1, v_k_2239_);
lean_ctor_set(v___x_2761_, 0, v___x_2769_);
v___x_2771_ = v___x_2761_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_r_2756_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_impl_2732_);
v___x_2771_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v___x_2771_);
lean_ctor_set(v___x_2749_, 3, v___y_2766_);
lean_ctor_set(v___x_2749_, 2, v_v_2754_);
lean_ctor_set(v___x_2749_, 1, v_k_2753_);
lean_ctor_set(v___x_2749_, 0, v___x_2764_);
v___x_2773_ = v___x_2749_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_k_2753_);
lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_v_2754_);
lean_ctor_set(v_reuseFailAlloc_2774_, 3, v___y_2766_);
lean_ctor_set(v_reuseFailAlloc_2774_, 4, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
v___jp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2779_ = lean_nat_add(v___x_2776_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec(v___x_2776_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_l_2755_);
lean_ctor_set(v___x_2244_, 3, v_l_2738_);
lean_ctor_set(v___x_2244_, 2, v_v_2737_);
lean_ctor_set(v___x_2244_, 1, v_k_2736_);
lean_ctor_set(v___x_2244_, 0, v___x_2779_);
v___x_2781_ = v___x_2244_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_k_2736_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_v_2737_);
lean_ctor_set(v_reuseFailAlloc_2785_, 3, v_l_2738_);
lean_ctor_set(v_reuseFailAlloc_2785_, 4, v_l_2755_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_nat_add(v___x_2733_, v_size_2734_);
if (lean_obj_tag(v_r_2756_) == 0)
{
lean_object* v_size_2783_; 
v_size_2783_ = lean_ctor_get(v_r_2756_, 0);
lean_inc(v_size_2783_);
v___y_2766_ = v___x_2781_;
v___y_2767_ = v___x_2782_;
v___y_2768_ = v_size_2783_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_unsigned_to_nat(0u);
v___y_2766_ = v___x_2781_;
v___y_2767_ = v___x_2782_;
v___y_2768_ = v___x_2784_;
goto v___jp_2765_;
}
}
}
}
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_del_object(v___x_2244_);
v___x_2794_ = lean_nat_add(v___x_2733_, v_size_2735_);
lean_dec(v_size_2735_);
v___x_2795_ = lean_nat_add(v___x_2794_, v_size_2734_);
lean_dec(v___x_2794_);
v___x_2796_ = lean_nat_add(v___x_2733_, v_size_2734_);
v___x_2797_ = lean_nat_add(v___x_2796_, v_size_2752_);
lean_dec(v___x_2796_);
lean_inc_ref(v_impl_2732_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v_impl_2732_);
lean_ctor_set(v___x_2749_, 3, v_r_2739_);
lean_ctor_set(v___x_2749_, 2, v_v_2240_);
lean_ctor_set(v___x_2749_, 1, v_k_2239_);
lean_ctor_set(v___x_2749_, 0, v___x_2797_);
v___x_2799_ = v___x_2749_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_r_2739_);
lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_impl_2732_);
v___x_2799_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_isSharedCheck_2806_ = !lean_is_exclusive(v_impl_2732_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; lean_object* v_unused_2811_; 
v_unused_2807_ = lean_ctor_get(v_impl_2732_, 4);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_impl_2732_, 3);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_impl_2732_, 2);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_impl_2732_, 1);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_impl_2732_, 0);
lean_dec(v_unused_2811_);
v___x_2801_ = v_impl_2732_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_dec(v_impl_2732_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 4, v___x_2799_);
lean_ctor_set(v___x_2801_, 3, v_l_2738_);
lean_ctor_set(v___x_2801_, 2, v_v_2737_);
lean_ctor_set(v___x_2801_, 1, v_k_2736_);
lean_ctor_set(v___x_2801_, 0, v___x_2795_);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_k_2736_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_v_2737_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_l_2738_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v___x_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
v_size_2819_ = lean_ctor_get(v_impl_2732_, 0);
v___x_2820_ = lean_nat_add(v___x_2733_, v_size_2819_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_impl_2732_);
lean_ctor_set(v___x_2244_, 0, v___x_2820_);
v___x_2822_ = v___x_2244_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2823_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2823_, 4, v_impl_2732_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
else
{
if (lean_obj_tag(v_l_2241_) == 0)
{
lean_object* v_l_2824_; 
v_l_2824_ = lean_ctor_get(v_l_2241_, 3);
if (lean_obj_tag(v_l_2824_) == 0)
{
lean_object* v_r_2825_; 
lean_inc_ref(v_l_2824_);
v_r_2825_ = lean_ctor_get(v_l_2241_, 4);
lean_inc(v_r_2825_);
if (lean_obj_tag(v_r_2825_) == 0)
{
lean_object* v_size_2826_; lean_object* v_k_2827_; lean_object* v_v_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2841_; 
v_size_2826_ = lean_ctor_get(v_l_2241_, 0);
v_k_2827_ = lean_ctor_get(v_l_2241_, 1);
v_v_2828_ = lean_ctor_get(v_l_2241_, 2);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; lean_object* v_unused_2843_; 
v_unused_2842_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2842_);
v_unused_2843_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2843_);
v___x_2830_ = v_l_2241_;
v_isShared_2831_ = v_isSharedCheck_2841_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_v_2828_);
lean_inc(v_k_2827_);
lean_inc(v_size_2826_);
lean_dec(v_l_2241_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2841_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v_size_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v_size_2832_ = lean_ctor_get(v_r_2825_, 0);
v___x_2833_ = lean_nat_add(v___x_2733_, v_size_2826_);
lean_dec(v_size_2826_);
v___x_2834_ = lean_nat_add(v___x_2733_, v_size_2832_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 4, v_impl_2732_);
lean_ctor_set(v___x_2830_, 3, v_r_2825_);
lean_ctor_set(v___x_2830_, 2, v_v_2240_);
lean_ctor_set(v___x_2830_, 1, v_k_2239_);
lean_ctor_set(v___x_2830_, 0, v___x_2834_);
v___x_2836_ = v___x_2830_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_r_2825_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_impl_2732_);
v___x_2836_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2838_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2836_);
lean_ctor_set(v___x_2244_, 3, v_l_2824_);
lean_ctor_set(v___x_2244_, 2, v_v_2828_);
lean_ctor_set(v___x_2244_, 1, v_k_2827_);
lean_ctor_set(v___x_2244_, 0, v___x_2833_);
v___x_2838_ = v___x_2244_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_k_2827_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_v_2828_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_l_2824_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
else
{
lean_object* v_k_2844_; lean_object* v_v_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2856_; 
v_k_2844_ = lean_ctor_get(v_l_2241_, 1);
v_v_2845_ = lean_ctor_get(v_l_2241_, 2);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; lean_object* v_unused_2858_; lean_object* v_unused_2859_; 
v_unused_2857_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2857_);
v_unused_2858_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2858_);
v_unused_2859_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2859_);
v___x_2847_ = v_l_2241_;
v_isShared_2848_ = v_isSharedCheck_2856_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_v_2845_);
lean_inc(v_k_2844_);
lean_dec(v_l_2241_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2856_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = lean_unsigned_to_nat(3u);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 3, v_r_2825_);
lean_ctor_set(v___x_2847_, 2, v_v_2240_);
lean_ctor_set(v___x_2847_, 1, v_k_2239_);
lean_ctor_set(v___x_2847_, 0, v___x_2733_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_r_2825_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v_r_2825_);
v___x_2851_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2853_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2851_);
lean_ctor_set(v___x_2244_, 3, v_l_2824_);
lean_ctor_set(v___x_2244_, 2, v_v_2845_);
lean_ctor_set(v___x_2244_, 1, v_k_2844_);
lean_ctor_set(v___x_2244_, 0, v___x_2849_);
v___x_2853_ = v___x_2244_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_k_2844_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_v_2845_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_l_2824_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
else
{
lean_object* v_r_2860_; 
v_r_2860_ = lean_ctor_get(v_l_2241_, 4);
lean_inc(v_r_2860_);
if (lean_obj_tag(v_r_2860_) == 0)
{
lean_object* v_k_2861_; lean_object* v_v_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2885_; 
lean_inc(v_l_2824_);
v_k_2861_ = lean_ctor_get(v_l_2241_, 1);
v_v_2862_ = lean_ctor_get(v_l_2241_, 2);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_l_2241_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; lean_object* v_unused_2887_; lean_object* v_unused_2888_; 
v_unused_2886_ = lean_ctor_get(v_l_2241_, 4);
lean_dec(v_unused_2886_);
v_unused_2887_ = lean_ctor_get(v_l_2241_, 3);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_l_2241_, 0);
lean_dec(v_unused_2888_);
v___x_2864_ = v_l_2241_;
v_isShared_2865_ = v_isSharedCheck_2885_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_v_2862_);
lean_inc(v_k_2861_);
lean_dec(v_l_2241_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2885_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_k_2866_; lean_object* v_v_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2881_; 
v_k_2866_ = lean_ctor_get(v_r_2860_, 1);
v_v_2867_ = lean_ctor_get(v_r_2860_, 2);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_r_2860_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; lean_object* v_unused_2883_; lean_object* v_unused_2884_; 
v_unused_2882_ = lean_ctor_get(v_r_2860_, 4);
lean_dec(v_unused_2882_);
v_unused_2883_ = lean_ctor_get(v_r_2860_, 3);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_r_2860_, 0);
lean_dec(v_unused_2884_);
v___x_2869_ = v_r_2860_;
v_isShared_2870_ = v_isSharedCheck_2881_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_v_2867_);
lean_inc(v_k_2866_);
lean_dec(v_r_2860_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2881_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2871_ = lean_unsigned_to_nat(3u);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 4, v_l_2824_);
lean_ctor_set(v___x_2869_, 3, v_l_2824_);
lean_ctor_set(v___x_2869_, 2, v_v_2862_);
lean_ctor_set(v___x_2869_, 1, v_k_2861_);
lean_ctor_set(v___x_2869_, 0, v___x_2733_);
v___x_2873_ = v___x_2869_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_k_2861_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_v_2862_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_l_2824_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_l_2824_);
v___x_2873_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2875_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 4, v_l_2824_);
lean_ctor_set(v___x_2864_, 2, v_v_2240_);
lean_ctor_set(v___x_2864_, 1, v_k_2239_);
lean_ctor_set(v___x_2864_, 0, v___x_2733_);
v___x_2875_ = v___x_2864_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_l_2824_);
lean_ctor_set(v_reuseFailAlloc_2879_, 4, v_l_2824_);
v___x_2875_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2877_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2875_);
lean_ctor_set(v___x_2244_, 3, v___x_2873_);
lean_ctor_set(v___x_2244_, 2, v_v_2867_);
lean_ctor_set(v___x_2244_, 1, v_k_2866_);
lean_ctor_set(v___x_2244_, 0, v___x_2871_);
v___x_2877_ = v___x_2244_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_k_2866_);
lean_ctor_set(v_reuseFailAlloc_2878_, 2, v_v_2867_);
lean_ctor_set(v_reuseFailAlloc_2878_, 3, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2878_, 4, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = lean_unsigned_to_nat(2u);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_r_2860_);
lean_ctor_set(v___x_2244_, 0, v___x_2889_);
v___x_2891_ = v___x_2244_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2892_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2892_, 4, v_r_2860_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v___x_2894_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v_l_2241_);
lean_ctor_set(v___x_2244_, 0, v___x_2733_);
v___x_2894_ = v___x_2244_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_l_2241_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_l_2241_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
}
else
{
return v_t_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_2898_, lean_object* v_t_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2898_, v_t_2899_);
lean_dec(v_k_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_2901_, lean_object* v_declName_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v_ext_2908_; lean_object* v_toEnvExtension_2909_; lean_object* v_env_2910_; lean_object* v_asyncMode_2911_; uint8_t v___x_2912_; lean_object* v___x_2913_; lean_object* v_funCC_2914_; lean_object* v___y_2916_; uint8_t v___x_2942_; 
v___x_2906_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2907_ = lean_st_ref_get(v_a_2904_);
v_ext_2908_ = lean_ctor_get(v_ext_2901_, 1);
v_toEnvExtension_2909_ = lean_ctor_get(v_ext_2908_, 0);
v_env_2910_ = lean_ctor_get(v___x_2907_, 0);
lean_inc_ref(v_env_2910_);
lean_dec(v___x_2907_);
v_asyncMode_2911_ = lean_ctor_get(v_toEnvExtension_2909_, 2);
v___x_2912_ = 0;
v___x_2913_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2906_, v_ext_2901_, v_env_2910_, v_asyncMode_2911_, v___x_2912_);
v_funCC_2914_ = lean_ctor_get(v___x_2913_, 2);
lean_inc(v_funCC_2914_);
lean_dec(v___x_2913_);
v___x_2942_ = l_Lean_NameSet_contains(v_funCC_2914_, v_declName_2902_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_inc(v_declName_2902_);
v___x_2943_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_dec_ref_known(v___x_2943_, 1);
v___y_2916_ = v_a_2904_;
goto v___jp_2915_;
}
else
{
lean_dec(v_funCC_2914_);
lean_dec(v_declName_2902_);
lean_dec_ref(v_ext_2901_);
return v___x_2943_;
}
}
else
{
v___y_2916_ = v_a_2904_;
goto v___jp_2915_;
}
v___jp_2915_:
{
lean_object* v___x_2917_; lean_object* v___f_2918_; lean_object* v___x_2919_; lean_object* v_env_2920_; lean_object* v_nextMacroScope_2921_; lean_object* v_ngen_2922_; lean_object* v_auxDeclNGen_2923_; lean_object* v_traceState_2924_; lean_object* v_recordedDeps_2925_; lean_object* v_messages_2926_; lean_object* v_infoState_2927_; lean_object* v_snapshotTasks_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2940_; 
v___x_2917_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_2902_, v_funCC_2914_);
lean_dec(v_declName_2902_);
v___f_2918_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_2918_, 0, v___x_2917_);
v___x_2919_ = lean_st_ref_take(v___y_2916_);
v_env_2920_ = lean_ctor_get(v___x_2919_, 0);
v_nextMacroScope_2921_ = lean_ctor_get(v___x_2919_, 1);
v_ngen_2922_ = lean_ctor_get(v___x_2919_, 2);
v_auxDeclNGen_2923_ = lean_ctor_get(v___x_2919_, 3);
v_traceState_2924_ = lean_ctor_get(v___x_2919_, 4);
v_recordedDeps_2925_ = lean_ctor_get(v___x_2919_, 6);
v_messages_2926_ = lean_ctor_get(v___x_2919_, 7);
v_infoState_2927_ = lean_ctor_get(v___x_2919_, 8);
v_snapshotTasks_2928_ = lean_ctor_get(v___x_2919_, 9);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2919_, 5);
lean_dec(v_unused_2941_);
v___x_2930_ = v___x_2919_;
v_isShared_2931_ = v_isSharedCheck_2940_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_snapshotTasks_2928_);
lean_inc(v_infoState_2927_);
lean_inc(v_messages_2926_);
lean_inc(v_recordedDeps_2925_);
lean_inc(v_traceState_2924_);
lean_inc(v_auxDeclNGen_2923_);
lean_inc(v_ngen_2922_);
lean_inc(v_nextMacroScope_2921_);
lean_inc(v_env_2920_);
lean_dec(v___x_2919_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2940_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2901_, v_env_2920_, v___f_2918_);
v___x_2934_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 5, v___x_2934_);
lean_ctor_set(v___x_2930_, 0, v___x_2933_);
v___x_2936_ = v___x_2930_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_nextMacroScope_2921_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_ngen_2922_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_auxDeclNGen_2923_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_traceState_2924_);
lean_ctor_set(v_reuseFailAlloc_2939_, 5, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2939_, 6, v_recordedDeps_2925_);
lean_ctor_set(v_reuseFailAlloc_2939_, 7, v_messages_2926_);
lean_ctor_set(v_reuseFailAlloc_2939_, 8, v_infoState_2927_);
lean_ctor_set(v_reuseFailAlloc_2939_, 9, v_snapshotTasks_2928_);
v___x_2936_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_st_ref_put(v___y_2916_, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2932_);
return v___x_2938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_2944_, lean_object* v_declName_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2944_, v_declName_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_2950_, lean_object* v_k_2951_, lean_object* v_t_2952_, lean_object* v_h_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2951_, v_t_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_2955_, lean_object* v_k_2956_, lean_object* v_t_2957_, lean_object* v_h_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_2955_, v_k_2956_, v_t_2957_, v_h_2958_);
lean_dec(v_k_2956_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_2960_, lean_object* v_s_2961_){
_start:
{
lean_object* v_casesTypes_2962_; lean_object* v_extThms_2963_; lean_object* v_funCC_2964_; lean_object* v_inj_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
v_casesTypes_2962_ = lean_ctor_get(v_s_2961_, 0);
v_extThms_2963_ = lean_ctor_get(v_s_2961_, 1);
v_funCC_2964_ = lean_ctor_get(v_s_2961_, 2);
v_inj_2965_ = lean_ctor_get(v_s_2961_, 4);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_s_2961_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; 
v_unused_2973_ = lean_ctor_get(v_s_2961_, 3);
lean_dec(v_unused_2973_);
v___x_2967_ = v_s_2961_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_inj_2965_);
lean_inc(v_funCC_2964_);
lean_inc(v_extThms_2963_);
lean_inc(v_casesTypes_2962_);
lean_dec(v_s_2961_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 3, v_a_2960_);
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_casesTypes_2962_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_extThms_2963_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_funCC_2964_);
lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_a_2960_);
lean_ctor_set(v_reuseFailAlloc_2971_, 4, v_inj_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_2974_, lean_object* v_declName_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_ext_2983_; lean_object* v_toEnvExtension_2984_; lean_object* v_env_2985_; lean_object* v_asyncMode_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v_ematch_2989_; lean_object* v___x_2990_; 
v___x_2981_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2982_ = lean_st_ref_get(v_a_2979_);
v_ext_2983_ = lean_ctor_get(v_ext_2974_, 1);
v_toEnvExtension_2984_ = lean_ctor_get(v_ext_2983_, 0);
v_env_2985_ = lean_ctor_get(v___x_2982_, 0);
lean_inc_ref(v_env_2985_);
lean_dec(v___x_2982_);
v_asyncMode_2986_ = lean_ctor_get(v_toEnvExtension_2984_, 2);
v___x_2987_ = 0;
v___x_2988_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2981_, v_ext_2974_, v_env_2985_, v_asyncMode_2986_, v___x_2987_);
v_ematch_2989_ = lean_ctor_get(v___x_2988_, 3);
lean_inc_ref(v_ematch_2989_);
lean_dec(v___x_2988_);
v___x_2990_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_2989_, v_declName_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3036_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_3036_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3036_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___f_2995_; lean_object* v___x_2996_; lean_object* v_env_2997_; lean_object* v_nextMacroScope_2998_; lean_object* v_ngen_2999_; lean_object* v_auxDeclNGen_3000_; lean_object* v_traceState_3001_; lean_object* v_recordedDeps_3002_; lean_object* v_messages_3003_; lean_object* v_infoState_3004_; lean_object* v_snapshotTasks_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3034_; 
v___f_2995_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_2995_, 0, v_a_2991_);
v___x_2996_ = lean_st_ref_take(v_a_2979_);
v_env_2997_ = lean_ctor_get(v___x_2996_, 0);
v_nextMacroScope_2998_ = lean_ctor_get(v___x_2996_, 1);
v_ngen_2999_ = lean_ctor_get(v___x_2996_, 2);
v_auxDeclNGen_3000_ = lean_ctor_get(v___x_2996_, 3);
v_traceState_3001_ = lean_ctor_get(v___x_2996_, 4);
v_recordedDeps_3002_ = lean_ctor_get(v___x_2996_, 6);
v_messages_3003_ = lean_ctor_get(v___x_2996_, 7);
v_infoState_3004_ = lean_ctor_get(v___x_2996_, 8);
v_snapshotTasks_3005_ = lean_ctor_get(v___x_2996_, 9);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v___x_2996_, 5);
lean_dec(v_unused_3035_);
v___x_3007_ = v___x_2996_;
v_isShared_3008_ = v_isSharedCheck_3034_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_snapshotTasks_3005_);
lean_inc(v_infoState_3004_);
lean_inc(v_messages_3003_);
lean_inc(v_recordedDeps_3002_);
lean_inc(v_traceState_3001_);
lean_inc(v_auxDeclNGen_3000_);
lean_inc(v_ngen_2999_);
lean_inc(v_nextMacroScope_2998_);
lean_inc(v_env_2997_);
lean_dec(v___x_2996_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3034_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3009_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2974_, v_env_2997_, v___f_2995_);
v___x_3010_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 5, v___x_3010_);
lean_ctor_set(v___x_3007_, 0, v___x_3009_);
v___x_3012_ = v___x_3007_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_nextMacroScope_2998_);
lean_ctor_set(v_reuseFailAlloc_3033_, 2, v_ngen_2999_);
lean_ctor_set(v_reuseFailAlloc_3033_, 3, v_auxDeclNGen_3000_);
lean_ctor_set(v_reuseFailAlloc_3033_, 4, v_traceState_3001_);
lean_ctor_set(v_reuseFailAlloc_3033_, 5, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3033_, 6, v_recordedDeps_3002_);
lean_ctor_set(v_reuseFailAlloc_3033_, 7, v_messages_3003_);
lean_ctor_set(v_reuseFailAlloc_3033_, 8, v_infoState_3004_);
lean_ctor_set(v_reuseFailAlloc_3033_, 9, v_snapshotTasks_3005_);
v___x_3012_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v_mctx_3015_; lean_object* v_zetaDeltaFVarIds_3016_; lean_object* v_postponed_3017_; lean_object* v_diag_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3031_; 
v___x_3013_ = lean_st_ref_put(v_a_2979_, v___x_3012_);
v___x_3014_ = lean_st_ref_take(v_a_2977_);
v_mctx_3015_ = lean_ctor_get(v___x_3014_, 0);
v_zetaDeltaFVarIds_3016_ = lean_ctor_get(v___x_3014_, 2);
v_postponed_3017_ = lean_ctor_get(v___x_3014_, 3);
v_diag_3018_ = lean_ctor_get(v___x_3014_, 4);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; 
v_unused_3032_ = lean_ctor_get(v___x_3014_, 1);
lean_dec(v_unused_3032_);
v___x_3020_ = v___x_3014_;
v_isShared_3021_ = v_isSharedCheck_3031_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_diag_3018_);
lean_inc(v_postponed_3017_);
lean_inc(v_zetaDeltaFVarIds_3016_);
lean_inc(v_mctx_3015_);
lean_dec(v___x_3014_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3031_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v___x_3023_);
v___x_3025_ = v___x_3020_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_mctx_3015_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_zetaDeltaFVarIds_3016_);
lean_ctor_set(v_reuseFailAlloc_3030_, 3, v_postponed_3017_);
lean_ctor_set(v_reuseFailAlloc_3030_, 4, v_diag_3018_);
v___x_3025_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3026_ = lean_st_ref_put(v_a_2977_, v___x_3025_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_3022_);
v___x_3028_ = v___x_2993_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3022_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v_ext_2974_);
v_a_3037_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2990_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2990_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_3045_, lean_object* v_declName_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3045_, v_declName_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_3053_, lean_object* v_s_3054_){
_start:
{
lean_object* v_casesTypes_3055_; lean_object* v_extThms_3056_; lean_object* v_funCC_3057_; lean_object* v_ematch_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_casesTypes_3055_ = lean_ctor_get(v_s_3054_, 0);
v_extThms_3056_ = lean_ctor_get(v_s_3054_, 1);
v_funCC_3057_ = lean_ctor_get(v_s_3054_, 2);
v_ematch_3058_ = lean_ctor_get(v_s_3054_, 3);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_s_3054_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v_s_3054_, 4);
lean_dec(v_unused_3066_);
v___x_3060_ = v_s_3054_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_ematch_3058_);
lean_inc(v_funCC_3057_);
lean_inc(v_extThms_3056_);
lean_inc(v_casesTypes_3055_);
lean_dec(v_s_3054_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 4, v_a_3053_);
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_casesTypes_3055_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_extThms_3056_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_funCC_3057_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_ematch_3058_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_a_3053_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_3067_, lean_object* v_declName_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v_ext_3076_; lean_object* v_toEnvExtension_3077_; lean_object* v_env_3078_; lean_object* v_asyncMode_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v_inj_3082_; lean_object* v___x_3083_; 
v___x_3074_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3075_ = lean_st_ref_get(v_a_3072_);
v_ext_3076_ = lean_ctor_get(v_ext_3067_, 1);
v_toEnvExtension_3077_ = lean_ctor_get(v_ext_3076_, 0);
v_env_3078_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_ref(v_env_3078_);
lean_dec(v___x_3075_);
v_asyncMode_3079_ = lean_ctor_get(v_toEnvExtension_3077_, 2);
v___x_3080_ = 0;
v___x_3081_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3074_, v_ext_3067_, v_env_3078_, v_asyncMode_3079_, v___x_3080_);
v_inj_3082_ = lean_ctor_get(v___x_3081_, 4);
lean_inc_ref(v_inj_3082_);
lean_dec(v___x_3081_);
v___x_3083_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_3082_, v_declName_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3129_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3129_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3129_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v_env_3090_; lean_object* v_nextMacroScope_3091_; lean_object* v_ngen_3092_; lean_object* v_auxDeclNGen_3093_; lean_object* v_traceState_3094_; lean_object* v_recordedDeps_3095_; lean_object* v_messages_3096_; lean_object* v_infoState_3097_; lean_object* v_snapshotTasks_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3127_; 
v___f_3088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_3088_, 0, v_a_3084_);
v___x_3089_ = lean_st_ref_take(v_a_3072_);
v_env_3090_ = lean_ctor_get(v___x_3089_, 0);
v_nextMacroScope_3091_ = lean_ctor_get(v___x_3089_, 1);
v_ngen_3092_ = lean_ctor_get(v___x_3089_, 2);
v_auxDeclNGen_3093_ = lean_ctor_get(v___x_3089_, 3);
v_traceState_3094_ = lean_ctor_get(v___x_3089_, 4);
v_recordedDeps_3095_ = lean_ctor_get(v___x_3089_, 6);
v_messages_3096_ = lean_ctor_get(v___x_3089_, 7);
v_infoState_3097_ = lean_ctor_get(v___x_3089_, 8);
v_snapshotTasks_3098_ = lean_ctor_get(v___x_3089_, 9);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3089_, 5);
lean_dec(v_unused_3128_);
v___x_3100_ = v___x_3089_;
v_isShared_3101_ = v_isSharedCheck_3127_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_snapshotTasks_3098_);
lean_inc(v_infoState_3097_);
lean_inc(v_messages_3096_);
lean_inc(v_recordedDeps_3095_);
lean_inc(v_traceState_3094_);
lean_inc(v_auxDeclNGen_3093_);
lean_inc(v_ngen_3092_);
lean_inc(v_nextMacroScope_3091_);
lean_inc(v_env_3090_);
lean_dec(v___x_3089_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3127_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3102_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_3067_, v_env_3090_, v___f_3088_);
v___x_3103_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 5, v___x_3103_);
lean_ctor_set(v___x_3100_, 0, v___x_3102_);
v___x_3105_ = v___x_3100_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_nextMacroScope_3091_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_ngen_3092_);
lean_ctor_set(v_reuseFailAlloc_3126_, 3, v_auxDeclNGen_3093_);
lean_ctor_set(v_reuseFailAlloc_3126_, 4, v_traceState_3094_);
lean_ctor_set(v_reuseFailAlloc_3126_, 5, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3126_, 6, v_recordedDeps_3095_);
lean_ctor_set(v_reuseFailAlloc_3126_, 7, v_messages_3096_);
lean_ctor_set(v_reuseFailAlloc_3126_, 8, v_infoState_3097_);
lean_ctor_set(v_reuseFailAlloc_3126_, 9, v_snapshotTasks_3098_);
v___x_3105_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v_mctx_3108_; lean_object* v_zetaDeltaFVarIds_3109_; lean_object* v_postponed_3110_; lean_object* v_diag_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3124_; 
v___x_3106_ = lean_st_ref_put(v_a_3072_, v___x_3105_);
v___x_3107_ = lean_st_ref_take(v_a_3070_);
v_mctx_3108_ = lean_ctor_get(v___x_3107_, 0);
v_zetaDeltaFVarIds_3109_ = lean_ctor_get(v___x_3107_, 2);
v_postponed_3110_ = lean_ctor_get(v___x_3107_, 3);
v_diag_3111_ = lean_ctor_get(v___x_3107_, 4);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v___x_3107_, 1);
lean_dec(v_unused_3125_);
v___x_3113_ = v___x_3107_;
v_isShared_3114_ = v_isSharedCheck_3124_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_diag_3111_);
lean_inc(v_postponed_3110_);
lean_inc(v_zetaDeltaFVarIds_3109_);
lean_inc(v_mctx_3108_);
lean_dec(v___x_3107_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3124_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3115_ = lean_box(0);
v___x_3116_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 1, v___x_3116_);
v___x_3118_ = v___x_3113_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_mctx_3108_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_zetaDeltaFVarIds_3109_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_postponed_3110_);
lean_ctor_set(v_reuseFailAlloc_3123_, 4, v_diag_3111_);
v___x_3118_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3119_ = lean_st_ref_put(v_a_3070_, v___x_3118_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3115_);
v___x_3121_ = v___x_3086_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3115_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref(v_ext_3067_);
v_a_3130_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3083_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3083_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_3138_, lean_object* v_declName_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3138_, v_declName_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
return v_res_3145_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3146_, lean_object* v_i_3147_, lean_object* v_k_3148_){
_start:
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = lean_array_get_size(v_keys_3146_);
v___x_3150_ = lean_nat_dec_lt(v_i_3147_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_dec(v_i_3147_);
return v___x_3150_;
}
else
{
lean_object* v_k_x27_3151_; uint8_t v___x_3152_; 
v_k_x27_3151_ = lean_array_fget_borrowed(v_keys_3146_, v_i_3147_);
v___x_3152_ = lean_name_eq(v_k_3148_, v_k_x27_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_nat_add(v_i_3147_, v___x_3153_);
lean_dec(v_i_3147_);
v_i_3147_ = v___x_3154_;
goto _start;
}
else
{
lean_dec(v_i_3147_);
return v___x_3150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3156_, lean_object* v_i_3157_, lean_object* v_k_3158_){
_start:
{
uint8_t v_res_3159_; lean_object* v_r_3160_; 
v_res_3159_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3156_, v_i_3157_, v_k_3158_);
lean_dec(v_k_3158_);
lean_dec_ref(v_keys_3156_);
v_r_3160_ = lean_box(v_res_3159_);
return v_r_3160_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_3161_, size_t v_x_3162_, lean_object* v_x_3163_){
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
lean_object* v_key_3170_; uint8_t v___x_3171_; 
v_key_3170_ = lean_ctor_get(v___x_3169_, 0);
v___x_3171_ = lean_name_eq(v_x_3163_, v_key_3170_);
return v___x_3171_;
}
case 1:
{
lean_object* v_node_3172_; size_t v___x_3173_; size_t v___x_3174_; 
v_node_3172_ = lean_ctor_get(v___x_3169_, 0);
v___x_3173_ = ((size_t)5ULL);
v___x_3174_ = lean_usize_shift_right(v_x_3162_, v___x_3173_);
v_x_3161_ = v_node_3172_;
v_x_3162_ = v___x_3174_;
goto _start;
}
default: 
{
uint8_t v___x_3176_; 
v___x_3176_ = 0;
return v___x_3176_;
}
}
}
else
{
lean_object* v_ks_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_ks_3177_ = lean_ctor_get(v_x_3161_, 0);
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_3177_, v___x_3178_, v_x_3163_);
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_3180_, lean_object* v_x_3181_, lean_object* v_x_3182_){
_start:
{
size_t v_x_330__boxed_3183_; uint8_t v_res_3184_; lean_object* v_r_3185_; 
v_x_330__boxed_3183_ = lean_unbox_usize(v_x_3181_);
lean_dec(v_x_3181_);
v_res_3184_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3180_, v_x_330__boxed_3183_, v_x_3182_);
lean_dec(v_x_3182_);
lean_dec_ref(v_x_3180_);
v_r_3185_ = lean_box(v_res_3184_);
return v_r_3185_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_3186_, lean_object* v_x_3187_){
_start:
{
uint64_t v___y_3189_; 
if (lean_obj_tag(v_x_3187_) == 0)
{
uint64_t v___x_3192_; 
v___x_3192_ = 1723ULL;
v___y_3189_ = v___x_3192_;
goto v___jp_3188_;
}
else
{
uint64_t v_hash_3193_; 
v_hash_3193_ = lean_ctor_get_uint64(v_x_3187_, sizeof(void*)*2);
v___y_3189_ = v_hash_3193_;
goto v___jp_3188_;
}
v___jp_3188_:
{
size_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = lean_uint64_to_usize(v___y_3189_);
v___x_3191_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3186_, v___x_3190_, v_x_3187_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3194_, v_x_3195_);
lean_dec(v_x_3195_);
lean_dec_ref(v_x_3194_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_3198_, lean_object* v_declName_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v_ext_3204_; lean_object* v_toEnvExtension_3205_; lean_object* v_env_3206_; lean_object* v_asyncMode_3207_; uint8_t v___x_3208_; lean_object* v___x_3209_; lean_object* v_extThms_3210_; uint8_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3202_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3203_ = lean_st_ref_get(v_a_3200_);
v_ext_3204_ = lean_ctor_get(v_ext_3198_, 1);
v_toEnvExtension_3205_ = lean_ctor_get(v_ext_3204_, 0);
v_env_3206_ = lean_ctor_get(v___x_3203_, 0);
lean_inc_ref(v_env_3206_);
lean_dec(v___x_3203_);
v_asyncMode_3207_ = lean_ctor_get(v_toEnvExtension_3205_, 2);
v___x_3208_ = 0;
v___x_3209_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3202_, v_ext_3198_, v_env_3206_, v_asyncMode_3207_, v___x_3208_);
v_extThms_3210_ = lean_ctor_get(v___x_3209_, 1);
lean_inc_ref(v_extThms_3210_);
lean_dec(v___x_3209_);
v___x_3211_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_3210_, v_declName_3199_);
lean_dec_ref(v_extThms_3210_);
v___x_3212_ = lean_box(v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_3214_, lean_object* v_declName_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3214_, v_declName_3215_, v_a_3216_);
lean_dec(v_a_3216_);
lean_dec(v_declName_3215_);
lean_dec_ref(v_ext_3214_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_3219_, lean_object* v_declName_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3219_, v_declName_3220_, v_a_3222_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_3225_, lean_object* v_declName_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_3225_, v_declName_3226_, v_a_3227_, v_a_3228_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_declName_3226_);
lean_dec_ref(v_ext_3225_);
return v_res_3230_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3232_, v_x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_){
_start:
{
uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_res_3238_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_3235_, v_x_3236_, v_x_3237_);
lean_dec(v_x_3237_);
lean_dec_ref(v_x_3236_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_3240_, lean_object* v_x_3241_, size_t v_x_3242_, lean_object* v_x_3243_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3241_, v_x_3242_, v_x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3245_, lean_object* v_x_3246_, lean_object* v_x_3247_, lean_object* v_x_3248_){
_start:
{
size_t v_x_417__boxed_3249_; uint8_t v_res_3250_; lean_object* v_r_3251_; 
v_x_417__boxed_3249_ = lean_unbox_usize(v_x_3247_);
lean_dec(v_x_3247_);
v_res_3250_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_3245_, v_x_3246_, v_x_417__boxed_3249_, v_x_3248_);
lean_dec(v_x_3248_);
lean_dec_ref(v_x_3246_);
v_r_3251_ = lean_box(v_res_3250_);
return v_r_3251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3252_, lean_object* v_keys_3253_, lean_object* v_vals_3254_, lean_object* v_heq_3255_, lean_object* v_i_3256_, lean_object* v_k_3257_){
_start:
{
uint8_t v___x_3258_; 
v___x_3258_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3253_, v_i_3256_, v_k_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3259_, lean_object* v_keys_3260_, lean_object* v_vals_3261_, lean_object* v_heq_3262_, lean_object* v_i_3263_, lean_object* v_k_3264_){
_start:
{
uint8_t v_res_3265_; lean_object* v_r_3266_; 
v_res_3265_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_3259_, v_keys_3260_, v_vals_3261_, v_heq_3262_, v_i_3263_, v_k_3264_);
lean_dec(v_k_3264_);
lean_dec_ref(v_vals_3261_);
lean_dec_ref(v_keys_3260_);
v_r_3266_ = lean_box(v_res_3265_);
return v_r_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_3267_, lean_object* v_declName_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v_ext_3273_; lean_object* v_toEnvExtension_3274_; lean_object* v_env_3275_; lean_object* v_asyncMode_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v_inj_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3271_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3272_ = lean_st_ref_get(v_a_3269_);
v_ext_3273_ = lean_ctor_get(v_ext_3267_, 1);
v_toEnvExtension_3274_ = lean_ctor_get(v_ext_3273_, 0);
v_env_3275_ = lean_ctor_get(v___x_3272_, 0);
lean_inc_ref(v_env_3275_);
lean_dec(v___x_3272_);
v_asyncMode_3276_ = lean_ctor_get(v_toEnvExtension_3274_, 2);
v___x_3277_ = 0;
v___x_3278_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3271_, v_ext_3267_, v_env_3275_, v_asyncMode_3276_, v___x_3277_);
v_inj_3279_ = lean_ctor_get(v___x_3278_, 4);
lean_inc_ref(v_inj_3279_);
lean_dec(v___x_3278_);
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_declName_3268_);
v___x_3281_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_3279_, v___x_3280_);
lean_dec_ref_known(v___x_3280_, 1);
lean_dec_ref(v_inj_3279_);
v___x_3282_ = lean_box(v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_3284_, lean_object* v_declName_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3284_, v_declName_3285_, v_a_3286_);
lean_dec(v_a_3286_);
lean_dec_ref(v_ext_3284_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_3289_, lean_object* v_declName_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3289_, v_declName_3290_, v_a_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_3295_, lean_object* v_declName_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_3295_, v_declName_3296_, v_a_3297_, v_a_3298_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec_ref(v_ext_3295_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_3301_, lean_object* v_declName_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v_ext_3307_; lean_object* v_toEnvExtension_3308_; lean_object* v_env_3309_; lean_object* v_asyncMode_3310_; uint8_t v___x_3311_; lean_object* v___x_3312_; lean_object* v_funCC_3313_; uint8_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3305_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3306_ = lean_st_ref_get(v_a_3303_);
v_ext_3307_ = lean_ctor_get(v_ext_3301_, 1);
v_toEnvExtension_3308_ = lean_ctor_get(v_ext_3307_, 0);
v_env_3309_ = lean_ctor_get(v___x_3306_, 0);
lean_inc_ref(v_env_3309_);
lean_dec(v___x_3306_);
v_asyncMode_3310_ = lean_ctor_get(v_toEnvExtension_3308_, 2);
v___x_3311_ = 0;
v___x_3312_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3305_, v_ext_3301_, v_env_3309_, v_asyncMode_3310_, v___x_3311_);
v_funCC_3313_ = lean_ctor_get(v___x_3312_, 2);
lean_inc(v_funCC_3313_);
lean_dec(v___x_3312_);
v___x_3314_ = l_Lean_NameSet_contains(v_funCC_3313_, v_declName_3302_);
lean_dec(v_funCC_3313_);
v___x_3315_ = lean_box(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_3317_, lean_object* v_declName_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3317_, v_declName_3318_, v_a_3319_);
lean_dec(v_a_3319_);
lean_dec(v_declName_3318_);
lean_dec_ref(v_ext_3317_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_3322_, lean_object* v_declName_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3322_, v_declName_3323_, v_a_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_3328_, lean_object* v_declName_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_3328_, v_declName_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_declName_3329_);
lean_dec_ref(v_ext_3328_);
return v_res_3333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_3358_ = l_Lean_mkAtom(v___x_3357_);
return v___x_3358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3361_ = lean_array_push(v___x_3360_, v___x_3359_);
return v___x_3361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_3371_ = l_Lean_mkAtom(v___x_3370_);
return v___x_3371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3374_ = lean_array_push(v___x_3373_, v___x_3372_);
return v___x_3374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3375_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_3376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_3377_ = lean_box(2);
v___x_3378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v___x_3376_);
lean_ctor_set(v___x_3378_, 2, v___x_3375_);
return v___x_3378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_3380_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_3381_ = lean_array_push(v___x_3380_, v___x_3379_);
return v___x_3381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_3384_ = lean_box(2);
v___x_3385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v___x_3383_);
lean_ctor_set(v___x_3385_, 2, v___x_3382_);
return v___x_3385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3388_ = lean_array_push(v___x_3387_, v___x_3386_);
return v___x_3388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_3391_ = lean_box(2);
v___x_3392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v___x_3390_);
lean_ctor_set(v___x_3392_, 2, v___x_3389_);
return v___x_3392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_3394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3395_ = lean_array_push(v___x_3394_, v___x_3393_);
return v___x_3395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_3397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_3398_ = lean_box(2);
v___x_3399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v___x_3397_);
lean_ctor_set(v___x_3399_, 2, v___x_3396_);
return v___x_3399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_3401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3402_ = lean_array_push(v___x_3401_, v___x_3400_);
return v___x_3402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_3405_ = lean_box(2);
v___x_3406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___x_3404_);
lean_ctor_set(v___x_3406_, 2, v___x_3403_);
return v___x_3406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_3408_, lean_object* v_ext_3409_, lean_object* v_____r_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = 0;
lean_inc(v_declName_3408_);
v___x_3417_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_3408_, v___x_3416_, v___y_3413_, v___y_3414_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; uint8_t v___x_3419_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
v___x_3419_ = lean_unbox(v_a_3418_);
lean_dec(v_a_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v_a_3421_; uint8_t v___x_3422_; 
v___x_3420_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3409_, v_declName_3408_, v___y_3414_);
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = lean_unbox(v_a_3421_);
lean_dec(v_a_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; lean_object* v_a_3424_; uint8_t v___x_3425_; 
lean_inc(v_declName_3408_);
v___x_3423_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3409_, v_declName_3408_, v___y_3414_);
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref(v___x_3423_);
v___x_3425_ = lean_unbox(v_a_3424_);
lean_dec(v_a_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v_a_3427_; uint8_t v___x_3428_; 
v___x_3426_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3409_, v_declName_3408_, v___y_3414_);
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = lean_unbox(v_a_3427_);
lean_dec(v_a_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3409_, v_declName_3408_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
return v___x_3429_;
}
else
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_3409_, v_declName_3408_, v___y_3413_, v___y_3414_);
return v___x_3430_;
}
}
else
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3409_, v_declName_3408_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
return v___x_3431_;
}
}
else
{
lean_object* v___x_3432_; 
v___x_3432_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_3409_, v_declName_3408_, v___y_3413_, v___y_3414_);
return v___x_3432_;
}
}
else
{
lean_object* v___x_3433_; 
v___x_3433_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_3409_, v_declName_3408_, v___y_3413_, v___y_3414_);
return v___x_3433_;
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_ext_3409_);
lean_dec(v_declName_3408_);
v_a_3434_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3417_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3417_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_3442_, lean_object* v_ext_3443_, lean_object* v_____r_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3442_, v_ext_3443_, v_____r_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_ref_3457_; lean_object* v___x_3458_; lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3467_; 
v_ref_3457_ = lean_ctor_get(v___y_3454_, 2);
v___x_3458_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3467_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
lean_inc(v_ref_3457_);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v_ref_3457_);
lean_ctor_set(v___x_3463_, 1, v_a_3459_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 1);
lean_ctor_set(v___x_3461_, 0, v___x_3463_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
return v_res_3474_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3481_; uint64_t v___x_3482_; 
v___x_3481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3482_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3481_);
return v___x_3482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_3484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3485_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set_uint64(v___x_3485_, sizeof(void*)*1, v___x_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3488_ = lean_box(1);
v___x_3489_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___x_3489_);
lean_ctor_set(v___x_3491_, 2, v___x_3488_);
return v___x_3491_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3494_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3496_ = lean_unsigned_to_nat(0u);
v___x_3497_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
lean_ctor_set(v___x_3497_, 2, v___x_3496_);
lean_ctor_set(v___x_3497_, 3, v___x_3496_);
lean_ctor_set(v___x_3497_, 4, v___x_3495_);
lean_ctor_set(v___x_3497_, 5, v___x_3495_);
lean_ctor_set(v___x_3497_, 6, v___x_3495_);
lean_ctor_set(v___x_3497_, 7, v___x_3495_);
lean_ctor_set(v___x_3497_, 8, v___x_3495_);
lean_ctor_set(v___x_3497_, 9, v___x_3495_);
lean_ctor_set(v___x_3497_, 10, v___x_3495_);
lean_ctor_set(v___x_3497_, 11, v___x_3494_);
return v___x_3497_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3499_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
lean_ctor_set(v___x_3499_, 2, v___x_3498_);
lean_ctor_set(v___x_3499_, 3, v___x_3498_);
lean_ctor_set(v___x_3499_, 4, v___x_3498_);
lean_ctor_set(v___x_3499_, 5, v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
lean_ctor_set(v___x_3501_, 2, v___x_3500_);
lean_ctor_set(v___x_3501_, 3, v___x_3500_);
lean_ctor_set(v___x_3501_, 4, v___x_3500_);
return v___x_3501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
return v___x_3504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_3507_ = l_Lean_stringToMessageData(v___x_3506_);
return v___x_3507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_3511_, lean_object* v___x_3512_, uint8_t v_showInfo_3513_, lean_object* v_attrName_3514_, lean_object* v_declName_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v___x_3519_; uint8_t v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___y_3534_; 
v___x_3519_ = 1;
v___x_3520_ = 0;
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3522_ = lean_unsigned_to_nat(0u);
v___x_3523_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3526_ = lean_box(0);
lean_inc(v___x_3512_);
v___x_3527_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3527_, 0, v___x_3521_);
lean_ctor_set(v___x_3527_, 1, v___x_3512_);
lean_ctor_set(v___x_3527_, 2, v___x_3524_);
lean_ctor_set(v___x_3527_, 3, v___x_3525_);
lean_ctor_set(v___x_3527_, 4, v___x_3526_);
lean_ctor_set(v___x_3527_, 5, v___x_3522_);
lean_ctor_set(v___x_3527_, 6, v___x_3526_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*7, v___x_3520_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*7 + 1, v___x_3520_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*7 + 2, v___x_3520_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*7 + 3, v___x_3519_);
v___x_3528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3528_);
lean_ctor_set(v___x_3531_, 1, v___x_3529_);
lean_ctor_set(v___x_3531_, 2, v___x_3512_);
lean_ctor_set(v___x_3531_, 3, v___x_3523_);
lean_ctor_set(v___x_3531_, 4, v___x_3530_);
v___x_3532_ = lean_st_mk_ref(v___x_3531_);
if (v_showInfo_3513_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v_attrName_3514_);
v___x_3544_ = lean_box(0);
v___x_3545_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3515_, v_ext_3511_, v___x_3544_, v___x_3527_, v___x_3532_, v___y_3516_, v___y_3517_);
lean_dec_ref_known(v___x_3527_, 7);
v___y_3534_ = v___x_3545_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec(v_declName_3515_);
lean_dec_ref(v_ext_3511_);
v___x_3546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_3547_ = l_Lean_MessageData_ofName(v_attrName_3514_);
lean_inc_ref(v___x_3547_);
v___x_3548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3548_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v___x_3547_);
v___x_3552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3553_, v___x_3527_, v___x_3532_, v___y_3516_, v___y_3517_);
lean_dec(v___x_3532_);
lean_dec_ref_known(v___x_3527_, 7);
return v___x_3554_;
}
v___jp_3533_:
{
if (lean_obj_tag(v___y_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3543_; 
v_a_3535_ = lean_ctor_get(v___y_3534_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___y_3534_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3537_ = v___y_3534_;
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___y_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3539_ = lean_st_ref_get(v___x_3532_);
lean_dec(v___x_3532_);
lean_dec(v___x_3539_);
if (v_isShared_3538_ == 0)
{
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3535_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_dec(v___x_3532_);
return v___y_3534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_3555_, lean_object* v___x_3556_, lean_object* v_showInfo_3557_, lean_object* v_attrName_3558_, lean_object* v_declName_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
uint8_t v_showInfo_boxed_3563_; lean_object* v_res_3564_; 
v_showInfo_boxed_3563_ = lean_unbox(v_showInfo_3557_);
v_res_3564_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_3555_, v___x_3556_, v_showInfo_boxed_3563_, v_attrName_3558_, v_declName_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_3567_, uint8_t v_attrKind_3568_, uint8_t v_showInfo_3569_, uint8_t v_minIndexable_3570_, lean_object* v_as_x27_3571_, lean_object* v_b_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
if (lean_obj_tag(v_as_x27_3571_) == 0)
{
lean_object* v___x_3578_; 
lean_dec_ref(v_ext_3567_);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_b_3572_);
return v___x_3578_;
}
else
{
lean_object* v_head_3579_; lean_object* v_tail_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v_head_3579_ = lean_ctor_get(v_as_x27_3571_, 0);
v_tail_3580_ = lean_ctor_get(v_as_x27_3571_, 1);
v___x_3581_ = lean_box(0);
v___x_3582_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3576_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_3579_);
lean_inc_ref(v_ext_3567_);
v___x_3585_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3567_, v_head_3579_, v_attrKind_3568_, v___x_3584_, v_a_3583_, v_showInfo_3569_, v_minIndexable_3570_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_dec_ref_known(v___x_3585_, 1);
v_as_x27_3571_ = v_tail_3580_;
v_b_3572_ = v___x_3581_;
goto _start;
}
else
{
lean_dec_ref(v_ext_3567_);
return v___x_3585_;
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v_ext_3567_);
v_a_3587_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3582_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3582_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_3595_, lean_object* v_attrKind_3596_, lean_object* v_showInfo_3597_, lean_object* v_minIndexable_3598_, lean_object* v_as_x27_3599_, lean_object* v_b_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
uint8_t v_attrKind_boxed_3606_; uint8_t v_showInfo_boxed_3607_; uint8_t v_minIndexable_boxed_3608_; lean_object* v_res_3609_; 
v_attrKind_boxed_3606_ = lean_unbox(v_attrKind_3596_);
v_showInfo_boxed_3607_ = lean_unbox(v_showInfo_3597_);
v_minIndexable_boxed_3608_ = lean_unbox(v_minIndexable_3598_);
v_res_3609_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3595_, v_attrKind_boxed_3606_, v_showInfo_boxed_3607_, v_minIndexable_boxed_3608_, v_as_x27_3599_, v_b_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v_as_x27_3599_);
return v_res_3609_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_3612_ = l_Lean_stringToMessageData(v___x_3611_);
return v___x_3612_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_3615_ = l_Lean_stringToMessageData(v___x_3614_);
return v___x_3615_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_3618_ = l_Lean_stringToMessageData(v___x_3617_);
return v___x_3618_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_3621_ = l_Lean_stringToMessageData(v___x_3620_);
return v___x_3621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_3626_ = l_Lean_stringToMessageData(v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_3629_ = l_Lean_stringToMessageData(v___x_3628_);
return v___x_3629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13));
v___x_3632_ = l_Lean_stringToMessageData(v___x_3631_);
return v___x_3632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15));
v___x_3635_ = l_Lean_stringToMessageData(v___x_3634_);
return v___x_3635_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17));
v___x_3638_ = l_Lean_stringToMessageData(v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_3639_, uint8_t v_attrKind_3640_, lean_object* v_stx_3641_, lean_object* v_ext_3642_, uint8_t v_showInfo_3643_, uint8_t v_minIndexable_3644_, uint8_t v___x_3645_, lean_object* v_attrName_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_3641_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___x_3674_, 1);
switch(lean_obj_tag(v_a_3675_))
{
case 0:
{
lean_object* v_k_3676_; 
lean_dec(v_attrName_3646_);
lean_dec(v_stx_3641_);
v_k_3676_ = lean_ctor_get(v_a_3675_, 0);
lean_inc(v_k_3676_);
lean_dec_ref_known(v_a_3675_, 1);
if (lean_obj_tag(v_k_3676_) == 9)
{
lean_object* v___x_3677_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_declName_3639_);
v___x_3677_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_3649_, v___y_3650_);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3650_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3680_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3642_, v_declName_3639_, v_attrKind_3640_, v_k_3676_, v_a_3679_, v_showInfo_3643_, v_minIndexable_3644_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3680_;
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec(v_k_3676_);
lean_dec_ref(v_ext_3642_);
lean_dec(v_declName_3639_);
v_a_3681_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3678_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3678_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_3689_; lean_object* v___x_3690_; 
lean_dec(v_attrName_3646_);
lean_dec(v_stx_3641_);
v_eager_3689_ = lean_ctor_get_uint8(v_a_3675_, 0);
lean_dec_ref_known(v_a_3675_, 0);
v___x_3690_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3642_, v_declName_3639_, v_eager_3689_, v_attrKind_3640_, v___y_3649_, v___y_3650_);
return v___x_3690_;
}
case 2:
{
lean_object* v___x_3691_; 
lean_dec(v_stx_3641_);
lean_inc(v_declName_3639_);
v___x_3691_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_3639_, v___x_3645_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3691_, 1);
if (lean_obj_tag(v_a_3692_) == 1)
{
lean_object* v_val_3693_; lean_object* v_ctors_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_dec(v_attrName_3646_);
lean_dec(v_declName_3639_);
v_val_3693_ = lean_ctor_get(v_a_3692_, 0);
lean_inc(v_val_3693_);
lean_dec_ref_known(v_a_3692_, 1);
v_ctors_3694_ = lean_ctor_get(v_val_3693_, 4);
lean_inc(v_ctors_3694_);
lean_dec(v_val_3693_);
v___x_3695_ = lean_box(0);
v___x_3696_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3642_, v_attrKind_3640_, v_showInfo_3643_, v_minIndexable_3644_, v_ctors_3694_, v___x_3695_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v_ctors_3694_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; 
v_unused_3704_ = lean_ctor_get(v___x_3696_, 0);
lean_dec(v_unused_3704_);
v___x_3698_ = v___x_3696_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_dec(v___x_3696_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3695_);
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3695_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
else
{
return v___x_3696_;
}
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_dec(v_a_3692_);
lean_dec_ref(v_ext_3642_);
v___x_3705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_3706_ = l_Lean_MessageData_ofName(v_attrName_3646_);
v___x_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3705_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = l_Lean_MessageData_ofConstName(v_declName_3639_, v___x_3645_);
v___x_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3713_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3714_;
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v_attrName_3646_);
lean_dec_ref(v_ext_3642_);
lean_dec(v_declName_3639_);
v_a_3715_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3691_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3691_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
case 3:
{
lean_object* v___x_3723_; 
lean_dec(v_attrName_3646_);
lean_inc(v_declName_3639_);
v___x_3723_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_3639_, v___x_3645_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
if (lean_obj_tag(v_a_3724_) == 1)
{
lean_object* v_val_3725_; lean_object* v___x_3726_; 
lean_dec(v_stx_3641_);
lean_dec(v_declName_3639_);
v_val_3725_ = lean_ctor_get(v_a_3724_, 0);
lean_inc_n(v_val_3725_, 2);
lean_dec_ref_known(v_a_3724_, 1);
lean_inc_ref(v_ext_3642_);
v___x_3726_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3642_, v_val_3725_, v___x_3645_, v_attrKind_3640_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3727_; 
lean_dec_ref_known(v___x_3726_, 1);
v___x_3727_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3725_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3748_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3730_ = v___x_3727_;
v_isShared_3731_ = v_isSharedCheck_3748_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3748_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
if (lean_obj_tag(v_a_3728_) == 1)
{
lean_object* v_val_3732_; lean_object* v_ctors_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_del_object(v___x_3730_);
v_val_3732_ = lean_ctor_get(v_a_3728_, 0);
lean_inc(v_val_3732_);
lean_dec_ref_known(v_a_3728_, 1);
v_ctors_3733_ = lean_ctor_get(v_val_3732_, 4);
lean_inc(v_ctors_3733_);
lean_dec(v_val_3732_);
v___x_3734_ = lean_box(0);
v___x_3735_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3642_, v_attrKind_3640_, v_showInfo_3643_, v_minIndexable_3644_, v_ctors_3733_, v___x_3734_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v_ctors_3733_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v___x_3735_, 0);
lean_dec(v_unused_3743_);
v___x_3737_ = v___x_3735_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v___x_3735_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3734_);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3734_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
else
{
return v___x_3735_;
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
lean_dec(v_a_3728_);
lean_dec_ref(v_ext_3642_);
v___x_3744_ = lean_box(0);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 0, v___x_3744_);
v___x_3746_ = v___x_3730_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v_ext_3642_);
v_a_3749_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3727_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3727_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_dec(v_val_3725_);
lean_dec_ref(v_ext_3642_);
return v___x_3726_;
}
}
else
{
lean_object* v___x_3757_; 
lean_dec(v_a_3724_);
v___x_3757_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3650_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3759_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___x_3759_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_3642_, v_stx_3641_, v_declName_3639_, v_attrKind_3640_, v_a_3758_, v_minIndexable_3644_, v_showInfo_3643_, v___x_3645_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3759_;
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
lean_dec(v_declName_3639_);
v_a_3760_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3757_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3757_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
lean_dec(v_declName_3639_);
v_a_3768_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3723_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3723_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
case 4:
{
lean_object* v___x_3776_; 
lean_dec(v_attrName_3646_);
lean_dec(v_stx_3641_);
v___x_3776_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_3642_, v_declName_3639_, v_attrKind_3640_, v___y_3649_, v___y_3650_);
return v___x_3776_;
}
case 5:
{
lean_object* v_prio_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
v_prio_3777_ = lean_ctor_get(v_a_3675_, 0);
lean_inc(v_prio_3777_);
lean_dec_ref_known(v_a_3675_, 1);
v___x_3778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3779_ = lean_name_eq(v_attrName_3646_, v___x_3778_);
lean_dec(v_attrName_3646_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_dec(v_prio_3777_);
lean_dec(v_declName_3639_);
v___x_3780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10);
v___x_3781_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3780_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3781_;
}
else
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_3639_, v_attrKind_3640_, v_prio_3777_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3782_;
}
}
case 6:
{
lean_object* v___x_3783_; 
lean_dec(v_attrName_3646_);
lean_dec(v_stx_3641_);
v___x_3783_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_3642_, v_declName_3639_, v_attrKind_3640_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3783_;
}
case 7:
{
lean_object* v___x_3784_; 
lean_dec(v_attrName_3646_);
lean_dec(v_stx_3641_);
v___x_3784_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_3642_, v_declName_3639_, v_attrKind_3640_, v___y_3649_, v___y_3650_);
return v___x_3784_;
}
case 8:
{
uint8_t v_post_3785_; uint8_t v_inv_3786_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
v_post_3785_ = lean_ctor_get_uint8(v_a_3675_, 0);
v_inv_3786_ = lean_ctor_get_uint8(v_a_3675_, 1);
lean_dec_ref_known(v_a_3675_, 0);
v___x_3794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3795_ = lean_name_eq(v_attrName_3646_, v___x_3794_);
lean_dec(v_attrName_3646_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_dec(v_declName_3639_);
v___x_3796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12);
v___x_3797_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3796_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3797_;
}
else
{
v___y_3788_ = v___y_3647_;
v___y_3789_ = v___y_3648_;
v___y_3790_ = v___y_3649_;
v___y_3791_ = v___y_3650_;
goto v___jp_3787_;
}
v___jp_3787_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = lean_unsigned_to_nat(1000u);
v___x_3793_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_3639_, v_post_3785_, v_inv_3786_, v_attrKind_3640_, v___x_3792_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
return v___x_3793_;
}
}
case 9:
{
lean_object* v___x_3798_; uint8_t v___x_3799_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
v___x_3798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3799_ = lean_name_eq(v_attrName_3646_, v___x_3798_);
lean_dec(v_attrName_3646_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec(v_declName_3639_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14);
v___x_3801_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3800_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3801_;
}
else
{
goto v___jp_3652_;
}
}
case 10:
{
uint8_t v_fallback_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
v_fallback_3802_ = lean_ctor_get_uint8(v_a_3675_, 0);
lean_dec_ref_known(v_a_3675_, 0);
v___x_3803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3804_ = lean_name_eq(v_attrName_3646_, v___x_3803_);
lean_dec(v_attrName_3646_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
lean_dec(v_declName_3639_);
v___x_3805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16);
v___x_3806_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3805_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3806_;
}
else
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_3639_, v_attrKind_3640_, v_fallback_3802_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3807_;
}
}
default: 
{
lean_object* v___x_3808_; uint8_t v___x_3809_; 
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3809_ = lean_name_eq(v_attrName_3646_, v___x_3808_);
lean_dec(v_attrName_3646_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
lean_dec(v_declName_3639_);
v___x_3810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18);
v___x_3811_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3810_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3811_;
}
else
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_3639_, v_attrKind_3640_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3812_;
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec(v_attrName_3646_);
lean_dec_ref(v_ext_3642_);
lean_dec(v_stx_3641_);
lean_dec(v_declName_3639_);
v_a_3813_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3674_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3674_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
v___jp_3652_:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_3639_, v_attrKind_3640_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3665_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3665_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3665_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
uint8_t v___x_3658_; 
v___x_3658_ = lean_unbox(v_a_3654_);
lean_dec(v_a_3654_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_del_object(v___x_3656_);
v___x_3659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_3660_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3659_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3660_;
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = lean_box(0);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3661_);
v___x_3663_ = v___x_3656_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
v_a_3666_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3653_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3653_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_3821_, lean_object* v_attrKind_3822_, lean_object* v_stx_3823_, lean_object* v_ext_3824_, lean_object* v_showInfo_3825_, lean_object* v_minIndexable_3826_, lean_object* v___x_3827_, lean_object* v_attrName_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
uint8_t v_attrKind_boxed_3834_; uint8_t v_showInfo_boxed_3835_; uint8_t v_minIndexable_boxed_3836_; uint8_t v___x_11386__boxed_3837_; lean_object* v_res_3838_; 
v_attrKind_boxed_3834_ = lean_unbox(v_attrKind_3822_);
v_showInfo_boxed_3835_ = lean_unbox(v_showInfo_3825_);
v_minIndexable_boxed_3836_ = lean_unbox(v_minIndexable_3826_);
v___x_11386__boxed_3837_ = lean_unbox(v___x_3827_);
v_res_3838_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_3821_, v_attrKind_boxed_3834_, v_stx_3823_, v_ext_3824_, v_showInfo_boxed_3835_, v_minIndexable_boxed_3836_, v___x_11386__boxed_3837_, v_attrName_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object* v___x_3839_, lean_object* v_entry_3840_, lean_object* v_s_3841_){
_start:
{
lean_object* v_addEntryFn_3842_; lean_object* v_importedEntries_3843_; lean_object* v_state_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3852_; 
v_addEntryFn_3842_ = lean_ctor_get(v___x_3839_, 3);
lean_inc(v_addEntryFn_3842_);
lean_dec_ref(v___x_3839_);
v_importedEntries_3843_ = lean_ctor_get(v_s_3841_, 0);
v_state_3844_ = lean_ctor_get(v_s_3841_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_s_3841_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3846_ = v_s_3841_;
v_isShared_3847_ = v_isSharedCheck_3852_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_state_3844_);
lean_inc(v_importedEntries_3843_);
lean_dec(v_s_3841_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3852_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v_state_3848_; lean_object* v___x_3850_; 
v_state_3848_ = lean_apply_2(v_addEntryFn_3842_, v_state_3844_, v_entry_3840_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 1, v_state_3848_);
v___x_3850_ = v___x_3846_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_importedEntries_3843_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_state_3848_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_3853_, lean_object* v_i_3854_, lean_object* v_k_3855_){
_start:
{
lean_object* v___x_3856_; uint8_t v___x_3857_; 
v___x_3856_ = lean_array_get_size(v_keys_3853_);
v___x_3857_ = lean_nat_dec_lt(v_i_3854_, v___x_3856_);
if (v___x_3857_ == 0)
{
lean_dec(v_i_3854_);
return v___x_3857_;
}
else
{
lean_object* v_k_x27_3858_; uint8_t v___x_3859_; 
v_k_x27_3858_ = lean_array_fget_borrowed(v_keys_3853_, v_i_3854_);
v___x_3859_ = l_Lean_instBEqExtraModUse_beq(v_k_3855_, v_k_x27_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_unsigned_to_nat(1u);
v___x_3861_ = lean_nat_add(v_i_3854_, v___x_3860_);
lean_dec(v_i_3854_);
v_i_3854_ = v___x_3861_;
goto _start;
}
else
{
lean_dec(v_i_3854_);
return v___x_3857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_3863_, lean_object* v_i_3864_, lean_object* v_k_3865_){
_start:
{
uint8_t v_res_3866_; lean_object* v_r_3867_; 
v_res_3866_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_3863_, v_i_3864_, v_k_3865_);
lean_dec_ref(v_k_3865_);
lean_dec_ref(v_keys_3863_);
v_r_3867_ = lean_box(v_res_3866_);
return v_r_3867_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3868_, size_t v_x_3869_, lean_object* v_x_3870_){
_start:
{
if (lean_obj_tag(v_x_3868_) == 0)
{
lean_object* v_es_3871_; lean_object* v___x_3872_; size_t v___x_3873_; size_t v___x_3874_; lean_object* v_j_3875_; lean_object* v___x_3876_; 
v_es_3871_ = lean_ctor_get(v_x_3868_, 0);
v___x_3872_ = lean_box(2);
v___x_3873_ = ((size_t)31ULL);
v___x_3874_ = lean_usize_land(v_x_3869_, v___x_3873_);
v_j_3875_ = lean_usize_to_nat(v___x_3874_);
v___x_3876_ = lean_array_get_borrowed(v___x_3872_, v_es_3871_, v_j_3875_);
lean_dec(v_j_3875_);
switch(lean_obj_tag(v___x_3876_))
{
case 0:
{
lean_object* v_key_3877_; uint8_t v___x_3878_; 
v_key_3877_ = lean_ctor_get(v___x_3876_, 0);
v___x_3878_ = l_Lean_instBEqExtraModUse_beq(v_x_3870_, v_key_3877_);
return v___x_3878_;
}
case 1:
{
lean_object* v_node_3879_; size_t v___x_3880_; size_t v___x_3881_; 
v_node_3879_ = lean_ctor_get(v___x_3876_, 0);
v___x_3880_ = ((size_t)5ULL);
v___x_3881_ = lean_usize_shift_right(v_x_3869_, v___x_3880_);
v_x_3868_ = v_node_3879_;
v_x_3869_ = v___x_3881_;
goto _start;
}
default: 
{
uint8_t v___x_3883_; 
v___x_3883_ = 0;
return v___x_3883_;
}
}
}
else
{
lean_object* v_ks_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; 
v_ks_3884_ = lean_ctor_get(v_x_3868_, 0);
v___x_3885_ = lean_unsigned_to_nat(0u);
v___x_3886_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_ks_3884_, v___x_3885_, v_x_3870_);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_3887_, lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
size_t v_x_11812__boxed_3890_; uint8_t v_res_3891_; lean_object* v_r_3892_; 
v_x_11812__boxed_3890_ = lean_unbox_usize(v_x_3888_);
lean_dec(v_x_3888_);
v_res_3891_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3887_, v_x_11812__boxed_3890_, v_x_3889_);
lean_dec_ref(v_x_3889_);
lean_dec_ref(v_x_3887_);
v_r_3892_ = lean_box(v_res_3891_);
return v_r_3892_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3893_, lean_object* v_x_3894_){
_start:
{
uint64_t v___x_3895_; size_t v___x_3896_; uint8_t v___x_3897_; 
v___x_3895_ = l_Lean_instHashableExtraModUse_hash(v_x_3894_);
v___x_3896_ = lean_uint64_to_usize(v___x_3895_);
v___x_3897_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3893_, v___x_3896_, v_x_3894_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3898_, lean_object* v_x_3899_){
_start:
{
uint8_t v_res_3900_; lean_object* v_r_3901_; 
v_res_3900_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_3898_, v_x_3899_);
lean_dec_ref(v_x_3899_);
lean_dec_ref(v_x_3898_);
v_r_3901_ = lean_box(v_res_3900_);
return v_r_3901_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_3902_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3));
v___x_3908_ = l_Lean_stringToMessageData(v___x_3907_);
return v___x_3908_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5));
v___x_3911_ = l_Lean_stringToMessageData(v___x_3910_);
return v___x_3911_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7(void){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_3913_ = l_Lean_stringToMessageData(v___x_3912_);
return v___x_3913_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v_cls_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_cls_3914_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_3915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_3916_ = l_Lean_Name_append(v___x_3915_, v_cls_3914_);
return v___x_3916_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9));
v___x_3919_ = l_Lean_stringToMessageData(v___x_3918_);
return v___x_3919_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12(void){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11));
v___x_3922_ = l_Lean_stringToMessageData(v___x_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object* v_mod_3927_, uint8_t v_isMeta_3928_, lean_object* v_hint_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v_env_3969_; uint8_t v_isExporting_3970_; lean_object* v_entry_3971_; lean_object* v___x_3972_; lean_object* v_env_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3967_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_3968_ = lean_st_ref_get(v___y_3933_);
v_env_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc_ref(v_env_3969_);
lean_dec(v___x_3968_);
v_isExporting_3970_ = lean_ctor_get_uint8(v_env_3969_, sizeof(void*)*13);
lean_dec_ref(v_env_3969_);
lean_inc(v_mod_3927_);
v_entry_3971_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3971_, 0, v_mod_3927_);
lean_ctor_set_uint8(v_entry_3971_, sizeof(void*)*1, v_isExporting_3970_);
lean_ctor_set_uint8(v_entry_3971_, sizeof(void*)*1 + 1, v_isMeta_3928_);
v___x_3972_ = lean_st_ref_get(v___y_3933_);
v_env_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc_ref(v_env_3973_);
lean_dec(v___x_3972_);
v___x_3974_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3975_ = lean_box(1);
v___x_3976_ = lean_box(0);
v___x_3977_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3967_, v___x_3974_, v_env_3973_, v___x_3975_, v___x_3976_);
v___x_3978_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_3977_, v_entry_3971_);
lean_dec(v___x_3977_);
if (v___x_3978_ == 0)
{
lean_object* v_toCold_3979_; lean_object* v_options_3980_; lean_object* v_inheritedTraceOptions_3981_; uint8_t v_hasTrace_3982_; lean_object* v___f_3983_; uint8_t v___x_3984_; lean_object* v___y_3986_; lean_object* v___y_3987_; 
v_toCold_3979_ = lean_ctor_get(v___y_3932_, 0);
v_options_3980_ = lean_ctor_get(v_toCold_3979_, 2);
v_inheritedTraceOptions_3981_ = lean_ctor_get(v_toCold_3979_, 11);
v_hasTrace_3982_ = lean_ctor_get_uint8(v_options_3980_, sizeof(void*)*1);
v___f_3983_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_3983_, 0, v___x_3974_);
lean_closure_set(v___f_3983_, 1, v_entry_3971_);
v___x_3984_ = 1;
if (v_hasTrace_3982_ == 0)
{
lean_dec(v_hint_3929_);
lean_dec(v_mod_3927_);
v___y_3986_ = v___y_3931_;
v___y_3987_ = v___y_3933_;
goto v___jp_3985_;
}
else
{
lean_object* v_cls_4014_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___x_4034_; uint8_t v___x_4035_; 
v_cls_4014_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4034_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3981_, v_options_3980_, v___x_4034_);
if (v___x_4035_ == 0)
{
lean_dec(v_hint_3929_);
lean_dec(v_mod_3927_);
v___y_3986_ = v___y_3931_;
v___y_3987_ = v___y_3933_;
goto v___jp_3985_;
}
else
{
lean_object* v___x_4036_; lean_object* v___y_4038_; 
v___x_4036_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_3970_ == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4038_ = v___x_4045_;
goto v___jp_4037_;
}
else
{
lean_object* v___x_4046_; 
v___x_4046_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4038_ = v___x_4046_;
goto v___jp_4037_;
}
v___jp_4037_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_inc_ref(v___y_4038_);
v___x_4039_ = l_Lean_stringToMessageData(v___y_4038_);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4036_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
if (v_isMeta_3928_ == 0)
{
lean_object* v___x_4043_; 
v___x_4043_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4021_ = v___x_4042_;
v___y_4022_ = v___x_4043_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4044_; 
v___x_4044_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4021_ = v___x_4042_;
v___y_4022_ = v___x_4044_;
goto v___jp_4020_;
}
}
}
v___jp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___y_4016_);
lean_ctor_set(v___x_4018_, 1, v___y_4017_);
v___x_4019_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_4014_, v___x_4018_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_dec_ref_known(v___x_4019_, 1);
v___y_3986_ = v___y_3931_;
v___y_3987_ = v___y_3933_;
goto v___jp_3985_;
}
else
{
lean_dec_ref(v___f_3983_);
return v___x_4019_;
}
}
v___jp_4020_:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
lean_inc_ref(v___y_4022_);
v___x_4023_ = l_Lean_stringToMessageData(v___y_4022_);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___y_4021_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
v___x_4025_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = l_Lean_MessageData_ofName(v_mod_3927_);
v___x_4028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4026_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = l_Lean_Name_isAnonymous(v_hint_3929_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4031_ = l_Lean_MessageData_ofName(v_hint_3929_);
v___x_4032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___y_4016_ = v___x_4028_;
v___y_4017_ = v___x_4032_;
goto v___jp_4015_;
}
else
{
lean_object* v___x_4033_; 
lean_dec(v_hint_3929_);
v___x_4033_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4016_ = v___x_4028_;
v___y_4017_ = v___x_4033_;
goto v___jp_4015_;
}
}
}
v___jp_3985_:
{
lean_object* v___x_3988_; lean_object* v_toEnvExtension_3989_; uint8_t v_logWrites_3990_; 
v___x_3988_ = lean_st_ref_take(v___y_3987_);
v_toEnvExtension_3989_ = lean_ctor_get(v___x_3974_, 0);
v_logWrites_3990_ = lean_ctor_get_uint8(v_toEnvExtension_3989_, sizeof(void*)*6);
if (v_logWrites_3990_ == 0)
{
lean_object* v_env_3991_; lean_object* v_nextMacroScope_3992_; lean_object* v_ngen_3993_; lean_object* v_auxDeclNGen_3994_; lean_object* v_traceState_3995_; lean_object* v_recordedDeps_3996_; lean_object* v_messages_3997_; lean_object* v_infoState_3998_; lean_object* v_snapshotTasks_3999_; lean_object* v_asyncMode_4000_; lean_object* v___x_4001_; 
v_env_3991_ = lean_ctor_get(v___x_3988_, 0);
lean_inc_ref(v_env_3991_);
v_nextMacroScope_3992_ = lean_ctor_get(v___x_3988_, 1);
lean_inc(v_nextMacroScope_3992_);
v_ngen_3993_ = lean_ctor_get(v___x_3988_, 2);
lean_inc_ref(v_ngen_3993_);
v_auxDeclNGen_3994_ = lean_ctor_get(v___x_3988_, 3);
lean_inc_ref(v_auxDeclNGen_3994_);
v_traceState_3995_ = lean_ctor_get(v___x_3988_, 4);
lean_inc_ref(v_traceState_3995_);
v_recordedDeps_3996_ = lean_ctor_get(v___x_3988_, 6);
lean_inc_ref(v_recordedDeps_3996_);
v_messages_3997_ = lean_ctor_get(v___x_3988_, 7);
lean_inc_ref(v_messages_3997_);
v_infoState_3998_ = lean_ctor_get(v___x_3988_, 8);
lean_inc_ref(v_infoState_3998_);
v_snapshotTasks_3999_ = lean_ctor_get(v___x_3988_, 9);
lean_inc_ref(v_snapshotTasks_3999_);
lean_dec(v___x_3988_);
v_asyncMode_4000_ = lean_ctor_get(v_toEnvExtension_3989_, 2);
lean_inc_ref(v_toEnvExtension_3989_);
v___x_4001_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3989_, v_env_3991_, v___f_3983_, v_asyncMode_4000_, v___x_3976_, v___x_3984_);
v___y_3936_ = v_snapshotTasks_3999_;
v___y_3937_ = v_ngen_3993_;
v___y_3938_ = v_auxDeclNGen_3994_;
v___y_3939_ = v_recordedDeps_3996_;
v___y_3940_ = v_nextMacroScope_3992_;
v___y_3941_ = v___y_3987_;
v___y_3942_ = v_traceState_3995_;
v___y_3943_ = v_messages_3997_;
v___y_3944_ = v___y_3986_;
v___y_3945_ = v_infoState_3998_;
v___y_3946_ = v___x_4001_;
goto v___jp_3935_;
}
else
{
lean_object* v_env_4002_; lean_object* v_nextMacroScope_4003_; lean_object* v_ngen_4004_; lean_object* v_auxDeclNGen_4005_; lean_object* v_traceState_4006_; lean_object* v_recordedDeps_4007_; lean_object* v_messages_4008_; lean_object* v_infoState_4009_; lean_object* v_snapshotTasks_4010_; lean_object* v_asyncMode_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_env_4002_ = lean_ctor_get(v___x_3988_, 0);
lean_inc_ref(v_env_4002_);
v_nextMacroScope_4003_ = lean_ctor_get(v___x_3988_, 1);
lean_inc(v_nextMacroScope_4003_);
v_ngen_4004_ = lean_ctor_get(v___x_3988_, 2);
lean_inc_ref(v_ngen_4004_);
v_auxDeclNGen_4005_ = lean_ctor_get(v___x_3988_, 3);
lean_inc_ref(v_auxDeclNGen_4005_);
v_traceState_4006_ = lean_ctor_get(v___x_3988_, 4);
lean_inc_ref(v_traceState_4006_);
v_recordedDeps_4007_ = lean_ctor_get(v___x_3988_, 6);
lean_inc_ref(v_recordedDeps_4007_);
v_messages_4008_ = lean_ctor_get(v___x_3988_, 7);
lean_inc_ref(v_messages_4008_);
v_infoState_4009_ = lean_ctor_get(v___x_3988_, 8);
lean_inc_ref(v_infoState_4009_);
v_snapshotTasks_4010_ = lean_ctor_get(v___x_3988_, 9);
lean_inc_ref(v_snapshotTasks_4010_);
lean_dec(v___x_3988_);
v_asyncMode_4011_ = lean_ctor_get(v_toEnvExtension_3989_, 2);
lean_inc_ref_n(v_toEnvExtension_3989_, 2);
v___x_4012_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3989_, v_env_4002_);
lean_dec_ref(v_env_4002_);
v___x_4013_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3989_, v___x_4012_, v___f_3983_, v_asyncMode_4011_, v___x_3976_, v___x_3984_);
v___y_3936_ = v_snapshotTasks_4010_;
v___y_3937_ = v_ngen_4004_;
v___y_3938_ = v_auxDeclNGen_4005_;
v___y_3939_ = v_recordedDeps_4007_;
v___y_3940_ = v_nextMacroScope_4003_;
v___y_3941_ = v___y_3987_;
v___y_3942_ = v_traceState_4006_;
v___y_3943_ = v_messages_4008_;
v___y_3944_ = v___y_3986_;
v___y_3945_ = v_infoState_4009_;
v___y_3946_ = v___x_4013_;
goto v___jp_3935_;
}
}
}
else
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_dec_ref_known(v_entry_3971_, 1);
lean_dec(v_hint_3929_);
lean_dec(v_mod_3927_);
v___x_4047_ = lean_box(0);
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
v___jp_3935_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v_mctx_3951_; lean_object* v_zetaDeltaFVarIds_3952_; lean_object* v_postponed_3953_; lean_object* v_diag_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3965_; 
v___x_3947_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
v___x_3948_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3948_, 0, v___y_3946_);
lean_ctor_set(v___x_3948_, 1, v___y_3940_);
lean_ctor_set(v___x_3948_, 2, v___y_3937_);
lean_ctor_set(v___x_3948_, 3, v___y_3938_);
lean_ctor_set(v___x_3948_, 4, v___y_3942_);
lean_ctor_set(v___x_3948_, 5, v___x_3947_);
lean_ctor_set(v___x_3948_, 6, v___y_3939_);
lean_ctor_set(v___x_3948_, 7, v___y_3943_);
lean_ctor_set(v___x_3948_, 8, v___y_3945_);
lean_ctor_set(v___x_3948_, 9, v___y_3936_);
v___x_3949_ = lean_st_ref_put(v___y_3941_, v___x_3948_);
v___x_3950_ = lean_st_ref_take(v___y_3944_);
v_mctx_3951_ = lean_ctor_get(v___x_3950_, 0);
v_zetaDeltaFVarIds_3952_ = lean_ctor_get(v___x_3950_, 2);
v_postponed_3953_ = lean_ctor_get(v___x_3950_, 3);
v_diag_3954_ = lean_ctor_get(v___x_3950_, 4);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; 
v_unused_3966_ = lean_ctor_get(v___x_3950_, 1);
lean_dec(v_unused_3966_);
v___x_3956_ = v___x_3950_;
v_isShared_3957_ = v_isSharedCheck_3965_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_diag_3954_);
lean_inc(v_postponed_3953_);
lean_inc(v_zetaDeltaFVarIds_3952_);
lean_inc(v_mctx_3951_);
lean_dec(v___x_3950_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3965_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3958_ = lean_box(0);
v___x_3959_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__2);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v___x_3959_);
v___x_3961_ = v___x_3956_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_mctx_3951_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_zetaDeltaFVarIds_3952_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_postponed_3953_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_diag_3954_);
v___x_3961_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_st_ref_put(v___y_3944_, v___x_3961_);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3958_);
return v___x_3963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object* v_mod_4049_, lean_object* v_isMeta_4050_, lean_object* v_hint_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
uint8_t v_isMeta_boxed_4057_; lean_object* v_res_4058_; 
v_isMeta_boxed_4057_ = lean_unbox(v_isMeta_4050_);
v_res_4058_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_mod_4049_, v_isMeta_boxed_4057_, v_hint_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object* v_a_4059_, lean_object* v_x_4060_){
_start:
{
if (lean_obj_tag(v_x_4060_) == 0)
{
lean_object* v___x_4061_; 
v___x_4061_ = lean_box(0);
return v___x_4061_;
}
else
{
lean_object* v_key_4062_; lean_object* v_value_4063_; lean_object* v_tail_4064_; uint8_t v___x_4065_; 
v_key_4062_ = lean_ctor_get(v_x_4060_, 0);
v_value_4063_ = lean_ctor_get(v_x_4060_, 1);
v_tail_4064_ = lean_ctor_get(v_x_4060_, 2);
v___x_4065_ = lean_name_eq(v_key_4062_, v_a_4059_);
if (v___x_4065_ == 0)
{
v_x_4060_ = v_tail_4064_;
goto _start;
}
else
{
lean_object* v___x_4067_; 
lean_inc(v_value_4063_);
v___x_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4067_, 0, v_value_4063_);
return v___x_4067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_4068_, lean_object* v_x_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4068_, v_x_4069_);
lean_dec(v_x_4069_);
lean_dec(v_a_4068_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object* v_m_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_buckets_4073_; lean_object* v___x_4074_; uint64_t v___y_4076_; 
v_buckets_4073_ = lean_ctor_get(v_m_4071_, 1);
v___x_4074_ = lean_array_get_size(v_buckets_4073_);
if (lean_obj_tag(v_a_4072_) == 0)
{
uint64_t v___x_4090_; 
v___x_4090_ = 1723ULL;
v___y_4076_ = v___x_4090_;
goto v___jp_4075_;
}
else
{
uint64_t v_hash_4091_; 
v_hash_4091_ = lean_ctor_get_uint64(v_a_4072_, sizeof(void*)*2);
v___y_4076_ = v_hash_4091_;
goto v___jp_4075_;
}
v___jp_4075_:
{
uint64_t v___x_4077_; uint64_t v___x_4078_; uint64_t v_fold_4079_; uint64_t v___x_4080_; uint64_t v___x_4081_; uint64_t v___x_4082_; size_t v___x_4083_; size_t v___x_4084_; size_t v___x_4085_; size_t v___x_4086_; size_t v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4077_ = 32ULL;
v___x_4078_ = lean_uint64_shift_right(v___y_4076_, v___x_4077_);
v_fold_4079_ = lean_uint64_xor(v___y_4076_, v___x_4078_);
v___x_4080_ = 16ULL;
v___x_4081_ = lean_uint64_shift_right(v_fold_4079_, v___x_4080_);
v___x_4082_ = lean_uint64_xor(v_fold_4079_, v___x_4081_);
v___x_4083_ = lean_uint64_to_usize(v___x_4082_);
v___x_4084_ = lean_usize_of_nat(v___x_4074_);
v___x_4085_ = ((size_t)1ULL);
v___x_4086_ = lean_usize_sub(v___x_4084_, v___x_4085_);
v___x_4087_ = lean_usize_land(v___x_4083_, v___x_4086_);
v___x_4088_ = lean_array_uget_borrowed(v_buckets_4073_, v___x_4087_);
v___x_4089_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4072_, v___x_4088_);
return v___x_4089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object* v_m_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_m_4092_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v___x_4095_, lean_object* v_declName_4096_, lean_object* v_as_4097_, size_t v_sz_4098_, size_t v_i_4099_, lean_object* v_b_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
uint8_t v___x_4106_; 
v___x_4106_ = lean_usize_dec_lt(v_i_4099_, v_sz_4098_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; 
lean_dec(v_declName_4096_);
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_b_4100_);
return v___x_4107_;
}
else
{
lean_object* v___x_4108_; lean_object* v_modules_4109_; lean_object* v___x_4110_; lean_object* v_a_4111_; lean_object* v___x_4112_; lean_object* v_toImport_4113_; lean_object* v_module_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; lean_object* v___x_4117_; 
v___x_4108_ = l_Lean_Environment_header(v___x_4095_);
v_modules_4109_ = lean_ctor_get(v___x_4108_, 3);
lean_inc_ref(v_modules_4109_);
lean_dec_ref(v___x_4108_);
v___x_4110_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4111_ = lean_array_uget_borrowed(v_as_4097_, v_i_4099_);
v___x_4112_ = lean_array_get(v___x_4110_, v_modules_4109_, v_a_4111_);
lean_dec_ref(v_modules_4109_);
v_toImport_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc_ref(v_toImport_4113_);
lean_dec(v___x_4112_);
v_module_4114_ = lean_ctor_get(v_toImport_4113_, 0);
lean_inc(v_module_4114_);
lean_dec_ref(v_toImport_4113_);
v___x_4115_ = lean_box(0);
v___x_4116_ = 0;
lean_inc(v_declName_4096_);
v___x_4117_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4114_, v___x_4116_, v_declName_4096_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4117_) == 0)
{
size_t v___x_4118_; size_t v___x_4119_; 
lean_dec_ref_known(v___x_4117_, 1);
v___x_4118_ = ((size_t)1ULL);
v___x_4119_ = lean_usize_add(v_i_4099_, v___x_4118_);
v_i_4099_ = v___x_4119_;
v_b_4100_ = v___x_4115_;
goto _start;
}
else
{
lean_dec(v_declName_4096_);
return v___x_4117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v___x_4121_, lean_object* v_declName_4122_, lean_object* v_as_4123_, lean_object* v_sz_4124_, lean_object* v_i_4125_, lean_object* v_b_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
size_t v_sz_boxed_4132_; size_t v_i_boxed_4133_; lean_object* v_res_4134_; 
v_sz_boxed_4132_ = lean_unbox_usize(v_sz_4124_);
lean_dec(v_sz_4124_);
v_i_boxed_4133_ = lean_unbox_usize(v_i_4125_);
lean_dec(v_i_4125_);
v_res_4134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v___x_4121_, v_declName_4122_, v_as_4123_, v_sz_boxed_4132_, v_i_boxed_4133_, v_b_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec_ref(v_as_4123_);
lean_dec_ref(v___x_4121_);
return v_res_4134_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Std_HashMap_instInhabited___redArg();
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_4138_, uint8_t v_isMeta_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v_env_4150_; lean_object* v___y_4152_; lean_object* v___x_4165_; 
v___x_4145_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4146_ = lean_st_ref_get(v___y_4143_);
v_env_4150_ = lean_ctor_get(v___x_4146_, 0);
lean_inc_ref(v_env_4150_);
lean_dec(v___x_4146_);
v___x_4165_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4150_, v_declName_4138_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_dec_ref(v_env_4150_);
lean_dec(v_declName_4138_);
goto v___jp_4147_;
}
else
{
lean_object* v_val_4166_; lean_object* v___x_4167_; lean_object* v_modules_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v_val_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_val_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4167_ = l_Lean_Environment_header(v_env_4150_);
v_modules_4168_ = lean_ctor_get(v___x_4167_, 3);
lean_inc_ref(v_modules_4168_);
lean_dec_ref(v___x_4167_);
v___x_4169_ = lean_array_get_size(v_modules_4168_);
v___x_4170_ = lean_nat_dec_lt(v_val_4166_, v___x_4169_);
if (v___x_4170_ == 0)
{
lean_dec_ref(v_modules_4168_);
lean_dec(v_val_4166_);
lean_dec_ref(v_env_4150_);
lean_dec(v_declName_4138_);
goto v___jp_4147_;
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___y_4174_; 
v___x_4171_ = lean_array_fget(v_modules_4168_, v_val_4166_);
lean_dec(v_val_4166_);
lean_dec_ref(v_modules_4168_);
v___x_4172_ = lean_st_ref_get(v___y_4143_);
if (v_isMeta_4139_ == 0)
{
lean_dec(v___x_4172_);
v___y_4174_ = v_isMeta_4139_;
goto v___jp_4173_;
}
else
{
lean_object* v_env_4185_; uint8_t v___x_4186_; 
v_env_4185_ = lean_ctor_get(v___x_4172_, 0);
lean_inc_ref(v_env_4185_);
lean_dec(v___x_4172_);
lean_inc(v_declName_4138_);
v___x_4186_ = l_Lean_isMarkedMeta(v_env_4185_, v_declName_4138_);
if (v___x_4186_ == 0)
{
v___y_4174_ = v_isMeta_4139_;
goto v___jp_4173_;
}
else
{
uint8_t v___x_4187_; 
v___x_4187_ = 0;
v___y_4174_ = v___x_4187_;
goto v___jp_4173_;
}
}
v___jp_4173_:
{
lean_object* v_toImport_4175_; lean_object* v_module_4176_; lean_object* v___x_4177_; 
v_toImport_4175_ = lean_ctor_get(v___x_4171_, 0);
lean_inc_ref(v_toImport_4175_);
lean_dec(v___x_4171_);
v_module_4176_ = lean_ctor_get(v_toImport_4175_, 0);
lean_inc(v_module_4176_);
lean_dec_ref(v_toImport_4175_);
lean_inc(v_declName_4138_);
v___x_4177_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4176_, v___y_4174_, v_declName_4138_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_dec_ref_known(v___x_4177_, 1);
v___x_4178_ = l_Lean_indirectModUseExt;
v___x_4179_ = lean_box(1);
v___x_4180_ = lean_box(0);
lean_inc_ref(v_env_4150_);
v___x_4181_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4145_, v___x_4178_, v_env_4150_, v___x_4179_, v___x_4180_);
v___x_4182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4181_, v_declName_4138_);
lean_dec(v___x_4181_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v___x_4183_; 
v___x_4183_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4152_ = v___x_4183_;
goto v___jp_4151_;
}
else
{
lean_object* v_val_4184_; 
v_val_4184_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_val_4184_);
lean_dec_ref_known(v___x_4182_, 1);
v___y_4152_ = v_val_4184_;
goto v___jp_4151_;
}
}
else
{
lean_dec_ref(v_env_4150_);
lean_dec(v_declName_4138_);
return v___x_4177_;
}
}
}
}
v___jp_4147_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_box(0);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
return v___x_4149_;
}
v___jp_4151_:
{
lean_object* v___x_4153_; size_t v_sz_4154_; size_t v___x_4155_; lean_object* v___x_4156_; 
v___x_4153_ = lean_box(0);
v_sz_4154_ = lean_array_size(v___y_4152_);
v___x_4155_ = ((size_t)0ULL);
v___x_4156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_env_4150_, v_declName_4138_, v___y_4152_, v_sz_4154_, v___x_4155_, v___x_4153_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_env_4150_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4163_ == 0)
{
lean_object* v_unused_4164_; 
v_unused_4164_ = lean_ctor_get(v___x_4156_, 0);
lean_dec(v_unused_4164_);
v___x_4158_ = v___x_4156_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_dec(v___x_4156_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v___x_4153_);
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4153_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
else
{
return v___x_4156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_4188_, lean_object* v_isMeta_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
uint8_t v_isMeta_boxed_4195_; lean_object* v_res_4196_; 
v_isMeta_boxed_4195_ = lean_unbox(v_isMeta_4189_);
v_res_4196_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4188_, v_isMeta_boxed_4195_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_4197_, uint8_t v_when_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
if (v_when_4198_ == 0)
{
lean_object* v___x_4204_; 
lean_inc(v___y_4202_);
lean_inc_ref(v___y_4201_);
lean_inc(v___y_4200_);
lean_inc_ref(v___y_4199_);
v___x_4204_ = lean_apply_5(v_x_4197_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, lean_box(0));
return v___x_4204_;
}
else
{
uint8_t v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = 0;
v___x_4206_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_4197_, v___x_4205_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
return v___x_4206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_4207_, lean_object* v_when_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v_when_boxed_4214_; lean_object* v_res_4215_; 
v_when_boxed_4214_ = lean_unbox(v_when_4208_);
v_res_4215_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4207_, v_when_boxed_4214_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_4216_, uint8_t v_showInfo_4217_, uint8_t v_minIndexable_4218_, lean_object* v_attrName_4219_, lean_object* v___x_4220_, lean_object* v_declName_4221_, lean_object* v_stx_4222_, uint8_t v_attrKind_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___f_4232_; uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4227_ = 0;
v___x_4228_ = lean_box(v_attrKind_4223_);
v___x_4229_ = lean_box(v_showInfo_4217_);
v___x_4230_ = lean_box(v_minIndexable_4218_);
v___x_4231_ = lean_box(v___x_4227_);
lean_inc(v_declName_4221_);
v___f_4232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_4232_, 0, v_declName_4221_);
lean_closure_set(v___f_4232_, 1, v___x_4228_);
lean_closure_set(v___f_4232_, 2, v_stx_4222_);
lean_closure_set(v___f_4232_, 3, v_ext_4216_);
lean_closure_set(v___f_4232_, 4, v___x_4229_);
lean_closure_set(v___f_4232_, 5, v___x_4230_);
lean_closure_set(v___f_4232_, 6, v___x_4231_);
lean_closure_set(v___f_4232_, 7, v_attrName_4219_);
v___x_4233_ = 1;
v___x_4234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_4235_ = lean_unsigned_to_nat(32u);
v___x_4236_ = lean_mk_empty_array_with_capacity(v___x_4235_);
lean_dec_ref(v___x_4236_);
v___x_4237_ = lean_unsigned_to_nat(0u);
v___x_4238_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_4239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_4240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_4241_ = lean_box(0);
lean_inc(v___x_4220_);
v___x_4242_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4242_, 0, v___x_4234_);
lean_ctor_set(v___x_4242_, 1, v___x_4220_);
lean_ctor_set(v___x_4242_, 2, v___x_4239_);
lean_ctor_set(v___x_4242_, 3, v___x_4240_);
lean_ctor_set(v___x_4242_, 4, v___x_4241_);
lean_ctor_set(v___x_4242_, 5, v___x_4237_);
lean_ctor_set(v___x_4242_, 6, v___x_4241_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*7, v___x_4227_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*7 + 1, v___x_4227_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*7 + 2, v___x_4227_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*7 + 3, v___x_4233_);
v___x_4243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_4244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_4245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_4246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4243_);
lean_ctor_set(v___x_4246_, 1, v___x_4244_);
lean_ctor_set(v___x_4246_, 2, v___x_4220_);
lean_ctor_set(v___x_4246_, 3, v___x_4238_);
lean_ctor_set(v___x_4246_, 4, v___x_4245_);
v___x_4247_ = lean_st_mk_ref(v___x_4246_);
v___x_4248_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4221_, v___x_4227_, v___x_4242_, v___x_4247_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v___x_4249_; 
lean_dec_ref_known(v___x_4248_, 1);
v___x_4249_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_4232_, v___x_4233_, v___x_4242_, v___x_4247_, v___y_4224_, v___y_4225_);
lean_dec_ref_known(v___x_4242_, 7);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4258_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4252_ = v___x_4249_;
v_isShared_4253_ = v_isSharedCheck_4258_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4249_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4258_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4254_; lean_object* v___x_4256_; 
v___x_4254_ = lean_st_ref_get(v___x_4247_);
lean_dec(v___x_4247_);
lean_dec(v___x_4254_);
if (v_isShared_4253_ == 0)
{
v___x_4256_ = v___x_4252_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4250_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
else
{
lean_dec(v___x_4247_);
return v___x_4249_;
}
}
else
{
lean_dec(v___x_4247_);
lean_dec_ref_known(v___x_4242_, 7);
lean_dec_ref(v___f_4232_);
return v___x_4248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_4259_, lean_object* v_showInfo_4260_, lean_object* v_minIndexable_4261_, lean_object* v_attrName_4262_, lean_object* v___x_4263_, lean_object* v_declName_4264_, lean_object* v_stx_4265_, lean_object* v_attrKind_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
uint8_t v_showInfo_boxed_4270_; uint8_t v_minIndexable_boxed_4271_; uint8_t v_attrKind_boxed_4272_; lean_object* v_res_4273_; 
v_showInfo_boxed_4270_ = lean_unbox(v_showInfo_4260_);
v_minIndexable_boxed_4271_ = lean_unbox(v_minIndexable_4261_);
v_attrKind_boxed_4272_ = lean_unbox(v_attrKind_4266_);
v_res_4273_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_4259_, v_showInfo_boxed_4270_, v_minIndexable_boxed_4271_, v_attrName_4262_, v___x_4263_, v_declName_4264_, v_stx_4265_, v_attrKind_boxed_4272_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_4296_, uint8_t v_minIndexable_4297_, uint8_t v_showInfo_4298_, lean_object* v_ext_4299_, lean_object* v_ref_4300_){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___f_4307_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4353_; 
v___x_4302_ = lean_box(1);
v___x_4303_ = lean_box(v_showInfo_4298_);
lean_inc_n(v_attrName_4296_, 2);
lean_inc_ref(v_ext_4299_);
v___f_4304_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4304_, 0, v_ext_4299_);
lean_closure_set(v___f_4304_, 1, v___x_4302_);
lean_closure_set(v___f_4304_, 2, v___x_4303_);
lean_closure_set(v___f_4304_, 3, v_attrName_4296_);
v___x_4305_ = lean_box(v_showInfo_4298_);
v___x_4306_ = lean_box(v_minIndexable_4297_);
v___f_4307_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_4307_, 0, v_ext_4299_);
lean_closure_set(v___f_4307_, 1, v___x_4305_);
lean_closure_set(v___f_4307_, 2, v___x_4306_);
lean_closure_set(v___f_4307_, 3, v_attrName_4296_);
lean_closure_set(v___f_4307_, 4, v___x_4302_);
if (v_minIndexable_4297_ == 0)
{
if (v_showInfo_4298_ == 0)
{
lean_inc(v_attrName_4296_);
v___y_4353_ = v_attrName_4296_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_4296_);
v___x_4382_ = lean_name_append_after(v_attrName_4296_, v___x_4381_);
v___y_4353_ = v___x_4382_;
goto v___jp_4352_;
}
}
else
{
if (v_showInfo_4298_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_4296_);
v___x_4384_ = lean_name_append_after(v_attrName_4296_, v___x_4383_);
v___y_4353_ = v___x_4384_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_4296_);
v___x_4386_ = lean_name_append_after(v_attrName_4296_, v___x_4385_);
v___y_4353_ = v___x_4386_;
goto v___jp_4352_;
}
}
v___jp_4308_:
{
lean_object* v___x_4311_; uint8_t v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; uint8_t v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_4312_ = 1;
v___x_4313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4296_, v___x_4312_);
v___x_4314_ = lean_string_append(v___x_4311_, v___x_4313_);
v___x_4315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_4316_ = lean_string_append(v___x_4314_, v___x_4315_);
v___x_4317_ = lean_string_append(v___x_4316_, v___x_4313_);
v___x_4318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_4319_ = lean_string_append(v___x_4317_, v___x_4318_);
v___x_4320_ = lean_string_append(v___x_4319_, v___x_4313_);
v___x_4321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_4322_ = lean_string_append(v___x_4320_, v___x_4321_);
v___x_4323_ = lean_string_append(v___x_4322_, v___x_4313_);
v___x_4324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_4325_ = lean_string_append(v___x_4323_, v___x_4324_);
v___x_4326_ = lean_string_append(v___x_4325_, v___x_4313_);
v___x_4327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_4328_ = lean_string_append(v___x_4326_, v___x_4327_);
v___x_4329_ = lean_string_append(v___x_4328_, v___x_4313_);
v___x_4330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_4331_ = lean_string_append(v___x_4329_, v___x_4330_);
v___x_4332_ = lean_string_append(v___x_4331_, v___x_4313_);
v___x_4333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_4334_ = lean_string_append(v___x_4332_, v___x_4333_);
v___x_4335_ = lean_string_append(v___x_4334_, v___x_4313_);
v___x_4336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_4337_ = lean_string_append(v___x_4335_, v___x_4336_);
v___x_4338_ = lean_string_append(v___x_4337_, v___x_4313_);
v___x_4339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_4340_ = lean_string_append(v___x_4338_, v___x_4339_);
v___x_4341_ = lean_string_append(v___x_4340_, v___x_4313_);
v___x_4342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_4343_ = lean_string_append(v___x_4341_, v___x_4342_);
v___x_4344_ = lean_string_append(v___x_4343_, v___x_4313_);
lean_dec_ref(v___x_4313_);
v___x_4345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_4346_ = lean_string_append(v___x_4344_, v___x_4345_);
v___x_4347_ = lean_string_append(v___y_4310_, v___x_4346_);
lean_dec_ref(v___x_4346_);
v___x_4348_ = 1;
v___x_4349_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4349_, 0, v_ref_4300_);
lean_ctor_set(v___x_4349_, 1, v___y_4309_);
lean_ctor_set(v___x_4349_, 2, v___x_4347_);
lean_ctor_set_uint8(v___x_4349_, sizeof(void*)*3, v___x_4348_);
v___x_4350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
lean_ctor_set(v___x_4350_, 1, v___f_4307_);
lean_ctor_set(v___x_4350_, 2, v___f_4304_);
v___x_4351_ = l_Lean_registerBuiltinAttribute(v___x_4350_);
return v___x_4351_;
}
v___jp_4352_:
{
if (v_minIndexable_4297_ == 0)
{
if (v_showInfo_4298_ == 0)
{
lean_object* v___x_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_4355_ = 1;
lean_inc(v_attrName_4296_);
v___x_4356_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4296_, v___x_4355_);
v___x_4357_ = lean_string_append(v___x_4354_, v___x_4356_);
lean_dec_ref(v___x_4356_);
v___x_4358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_4359_ = lean_string_append(v___x_4357_, v___x_4358_);
v___y_4309_ = v___y_4353_;
v___y_4310_ = v___x_4359_;
goto v___jp_4308_;
}
else
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4296_);
v___x_4361_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4296_, v_showInfo_4298_);
v___x_4362_ = lean_string_append(v___x_4360_, v___x_4361_);
v___x_4363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_4364_ = lean_string_append(v___x_4362_, v___x_4363_);
v___x_4365_ = lean_string_append(v___x_4364_, v___x_4361_);
lean_dec_ref(v___x_4361_);
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_4367_ = lean_string_append(v___x_4365_, v___x_4366_);
v___y_4309_ = v___y_4353_;
v___y_4310_ = v___x_4367_;
goto v___jp_4308_;
}
}
else
{
if (v_showInfo_4298_ == 0)
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4296_);
v___x_4369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4296_, v_minIndexable_4297_);
v___x_4370_ = lean_string_append(v___x_4368_, v___x_4369_);
lean_dec_ref(v___x_4369_);
v___x_4371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_4372_ = lean_string_append(v___x_4370_, v___x_4371_);
v___y_4309_ = v___y_4353_;
v___y_4310_ = v___x_4372_;
goto v___jp_4308_;
}
else
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4296_);
v___x_4374_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4296_, v_showInfo_4298_);
v___x_4375_ = lean_string_append(v___x_4373_, v___x_4374_);
v___x_4376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_4377_ = lean_string_append(v___x_4375_, v___x_4376_);
v___x_4378_ = lean_string_append(v___x_4377_, v___x_4374_);
lean_dec_ref(v___x_4374_);
v___x_4379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_4380_ = lean_string_append(v___x_4378_, v___x_4379_);
v___y_4309_ = v___y_4353_;
v___y_4310_ = v___x_4380_;
goto v___jp_4308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_4387_, lean_object* v_minIndexable_4388_, lean_object* v_showInfo_4389_, lean_object* v_ext_4390_, lean_object* v_ref_4391_, lean_object* v_a_4392_){
_start:
{
uint8_t v_minIndexable_boxed_4393_; uint8_t v_showInfo_boxed_4394_; lean_object* v_res_4395_; 
v_minIndexable_boxed_4393_ = lean_unbox(v_minIndexable_4388_);
v_showInfo_boxed_4394_ = lean_unbox(v_showInfo_4389_);
v_res_4395_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4387_, v_minIndexable_boxed_4393_, v_showInfo_boxed_4394_, v_ext_4390_, v_ref_4391_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_4396_, lean_object* v_msg_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_4404_, lean_object* v_msg_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_4404_, v_msg_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_4412_, uint8_t v_attrKind_4413_, uint8_t v_showInfo_4414_, uint8_t v_minIndexable_4415_, lean_object* v_as_4416_, lean_object* v_as_x27_4417_, lean_object* v_b_4418_, lean_object* v_a_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v___x_4425_; 
v___x_4425_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_4412_, v_attrKind_4413_, v_showInfo_4414_, v_minIndexable_4415_, v_as_x27_4417_, v_b_4418_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_4426_, lean_object* v_attrKind_4427_, lean_object* v_showInfo_4428_, lean_object* v_minIndexable_4429_, lean_object* v_as_4430_, lean_object* v_as_x27_4431_, lean_object* v_b_4432_, lean_object* v_a_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
uint8_t v_attrKind_boxed_4439_; uint8_t v_showInfo_boxed_4440_; uint8_t v_minIndexable_boxed_4441_; lean_object* v_res_4442_; 
v_attrKind_boxed_4439_ = lean_unbox(v_attrKind_4427_);
v_showInfo_boxed_4440_ = lean_unbox(v_showInfo_4428_);
v_minIndexable_boxed_4441_ = lean_unbox(v_minIndexable_4429_);
v_res_4442_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_4426_, v_attrKind_boxed_4439_, v_showInfo_boxed_4440_, v_minIndexable_boxed_4441_, v_as_4430_, v_as_x27_4431_, v_b_4432_, v_a_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v_as_x27_4431_);
lean_dec(v_as_4430_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_4443_, lean_object* v_x_4444_, uint8_t v_when_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4444_, v_when_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_4452_, lean_object* v_x_4453_, lean_object* v_when_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
uint8_t v_when_boxed_4460_; lean_object* v_res_4461_; 
v_when_boxed_4460_ = lean_unbox(v_when_4454_);
v_res_4461_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_4452_, v_x_4453_, v_when_boxed_4460_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v_00_u03b2_4462_, lean_object* v_m_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4463_, v_a_4464_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4466_, lean_object* v_m_4467_, lean_object* v_a_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_00_u03b2_4466_, v_m_4467_, v_a_4468_);
lean_dec(v_a_4468_);
lean_dec_ref(v_m_4467_);
return v_res_4469_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_4470_, lean_object* v_x_4471_, lean_object* v_x_4472_){
_start:
{
uint8_t v___x_4473_; 
v___x_4473_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_4471_, v_x_4472_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4474_, lean_object* v_x_4475_, lean_object* v_x_4476_){
_start:
{
uint8_t v_res_4477_; lean_object* v_r_4478_; 
v_res_4477_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(v_00_u03b2_4474_, v_x_4475_, v_x_4476_);
lean_dec_ref(v_x_4476_);
lean_dec_ref(v_x_4475_);
v_r_4478_ = lean_box(v_res_4477_);
return v_r_4478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4479_, lean_object* v_a_4480_, lean_object* v_x_4481_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4480_, v_x_4481_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4483_, lean_object* v_a_4484_, lean_object* v_x_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(v_00_u03b2_4483_, v_a_4484_, v_x_4485_);
lean_dec(v_x_4485_);
lean_dec(v_a_4484_);
return v_res_4486_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4487_, lean_object* v_x_4488_, size_t v_x_4489_, lean_object* v_x_4490_){
_start:
{
uint8_t v___x_4491_; 
v___x_4491_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_4488_, v_x_4489_, v_x_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4492_, lean_object* v_x_4493_, lean_object* v_x_4494_, lean_object* v_x_4495_){
_start:
{
size_t v_x_12823__boxed_4496_; uint8_t v_res_4497_; lean_object* v_r_4498_; 
v_x_12823__boxed_4496_ = lean_unbox_usize(v_x_4494_);
lean_dec(v_x_4494_);
v_res_4497_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(v_00_u03b2_4492_, v_x_4493_, v_x_12823__boxed_4496_, v_x_4495_);
lean_dec_ref(v_x_4495_);
lean_dec_ref(v_x_4493_);
v_r_4498_ = lean_box(v_res_4497_);
return v_r_4498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4499_, lean_object* v_keys_4500_, lean_object* v_vals_4501_, lean_object* v_heq_4502_, lean_object* v_i_4503_, lean_object* v_k_4504_){
_start:
{
uint8_t v___x_4505_; 
v___x_4505_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_4500_, v_i_4503_, v_k_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_4506_, lean_object* v_keys_4507_, lean_object* v_vals_4508_, lean_object* v_heq_4509_, lean_object* v_i_4510_, lean_object* v_k_4511_){
_start:
{
uint8_t v_res_4512_; lean_object* v_r_4513_; 
v_res_4512_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(v_00_u03b2_4506_, v_keys_4507_, v_vals_4508_, v_heq_4509_, v_i_4510_, v_k_4511_);
lean_dec_ref(v_k_4511_);
lean_dec_ref(v_vals_4508_);
lean_dec_ref(v_keys_4507_);
v_r_4513_ = lean_box(v_res_4512_);
return v_r_4513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = lean_box(0);
v___x_4515_ = lean_unsigned_to_nat(16u);
v___x_4516_ = lean_mk_array(v___x_4515_, v___x_4514_);
return v___x_4516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4518_ = lean_unsigned_to_nat(0u);
v___x_4519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
lean_ctor_set(v___x_4519_, 1, v___x_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4522_ = lean_st_mk_ref(v___x_4521_);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_4526_, lean_object* v_msg_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v_ref_4531_; lean_object* v___x_4532_; lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4578_; 
v_ref_4531_ = lean_ctor_get(v___y_4528_, 2);
v___x_4532_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_4527_, v___y_4528_, v___y_4529_);
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4578_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4578_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4537_; lean_object* v_traceState_4538_; lean_object* v_env_4539_; lean_object* v_nextMacroScope_4540_; lean_object* v_ngen_4541_; lean_object* v_auxDeclNGen_4542_; lean_object* v_cache_4543_; lean_object* v_recordedDeps_4544_; lean_object* v_messages_4545_; lean_object* v_infoState_4546_; lean_object* v_snapshotTasks_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4577_; 
v___x_4537_ = lean_st_ref_take(v___y_4529_);
v_traceState_4538_ = lean_ctor_get(v___x_4537_, 4);
v_env_4539_ = lean_ctor_get(v___x_4537_, 0);
v_nextMacroScope_4540_ = lean_ctor_get(v___x_4537_, 1);
v_ngen_4541_ = lean_ctor_get(v___x_4537_, 2);
v_auxDeclNGen_4542_ = lean_ctor_get(v___x_4537_, 3);
v_cache_4543_ = lean_ctor_get(v___x_4537_, 5);
v_recordedDeps_4544_ = lean_ctor_get(v___x_4537_, 6);
v_messages_4545_ = lean_ctor_get(v___x_4537_, 7);
v_infoState_4546_ = lean_ctor_get(v___x_4537_, 8);
v_snapshotTasks_4547_ = lean_ctor_get(v___x_4537_, 9);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4549_ = v___x_4537_;
v_isShared_4550_ = v_isSharedCheck_4577_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_snapshotTasks_4547_);
lean_inc(v_infoState_4546_);
lean_inc(v_messages_4545_);
lean_inc(v_recordedDeps_4544_);
lean_inc(v_cache_4543_);
lean_inc(v_traceState_4538_);
lean_inc(v_auxDeclNGen_4542_);
lean_inc(v_ngen_4541_);
lean_inc(v_nextMacroScope_4540_);
lean_inc(v_env_4539_);
lean_dec(v___x_4537_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4577_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
uint64_t v_tid_4551_; lean_object* v_traces_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4576_; 
v_tid_4551_ = lean_ctor_get_uint64(v_traceState_4538_, sizeof(void*)*1);
v_traces_4552_ = lean_ctor_get(v_traceState_4538_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_traceState_4538_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4554_ = v_traceState_4538_;
v_isShared_4555_ = v_isSharedCheck_4576_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_traces_4552_);
lean_dec(v_traceState_4538_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4576_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; double v___x_4558_; uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4556_ = lean_box(0);
v___x_4557_ = lean_box(0);
v___x_4558_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_4559_ = 0;
v___x_4560_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_4561_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4561_, 0, v_cls_4526_);
lean_ctor_set(v___x_4561_, 1, v___x_4557_);
lean_ctor_set(v___x_4561_, 2, v___x_4560_);
lean_ctor_set_float(v___x_4561_, sizeof(void*)*3, v___x_4558_);
lean_ctor_set_float(v___x_4561_, sizeof(void*)*3 + 8, v___x_4558_);
lean_ctor_set_uint8(v___x_4561_, sizeof(void*)*3 + 16, v___x_4559_);
v___x_4562_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_4563_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4561_);
lean_ctor_set(v___x_4563_, 1, v_a_4533_);
lean_ctor_set(v___x_4563_, 2, v___x_4562_);
lean_inc(v_ref_4531_);
v___x_4564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4564_, 0, v_ref_4531_);
lean_ctor_set(v___x_4564_, 1, v___x_4563_);
v___x_4565_ = l_Lean_PersistentArray_push___redArg(v_traces_4552_, v___x_4564_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4565_);
v___x_4567_ = v___x_4554_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4565_);
lean_ctor_set_uint64(v_reuseFailAlloc_4575_, sizeof(void*)*1, v_tid_4551_);
v___x_4567_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4569_; 
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 4, v___x_4567_);
v___x_4569_ = v___x_4549_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_env_4539_);
lean_ctor_set(v_reuseFailAlloc_4574_, 1, v_nextMacroScope_4540_);
lean_ctor_set(v_reuseFailAlloc_4574_, 2, v_ngen_4541_);
lean_ctor_set(v_reuseFailAlloc_4574_, 3, v_auxDeclNGen_4542_);
lean_ctor_set(v_reuseFailAlloc_4574_, 4, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4574_, 5, v_cache_4543_);
lean_ctor_set(v_reuseFailAlloc_4574_, 6, v_recordedDeps_4544_);
lean_ctor_set(v_reuseFailAlloc_4574_, 7, v_messages_4545_);
lean_ctor_set(v_reuseFailAlloc_4574_, 8, v_infoState_4546_);
lean_ctor_set(v_reuseFailAlloc_4574_, 9, v_snapshotTasks_4547_);
v___x_4569_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4570_; lean_object* v___x_4572_; 
v___x_4570_ = lean_st_ref_put(v___y_4529_, v___x_4569_);
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 0, v___x_4556_);
v___x_4572_ = v___x_4535_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4556_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_4579_, lean_object* v_msg_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4579_, v_msg_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_4585_, uint8_t v_isMeta_4586_, lean_object* v_hint_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v_env_4609_; uint8_t v_isExporting_4610_; lean_object* v_entry_4611_; lean_object* v___x_4612_; lean_object* v_env_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; uint8_t v___x_4618_; 
v___x_4607_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_4608_ = lean_st_ref_get(v___y_4589_);
v_env_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc_ref(v_env_4609_);
lean_dec(v___x_4608_);
v_isExporting_4610_ = lean_ctor_get_uint8(v_env_4609_, sizeof(void*)*13);
lean_dec_ref(v_env_4609_);
lean_inc(v_mod_4585_);
v_entry_4611_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4611_, 0, v_mod_4585_);
lean_ctor_set_uint8(v_entry_4611_, sizeof(void*)*1, v_isExporting_4610_);
lean_ctor_set_uint8(v_entry_4611_, sizeof(void*)*1 + 1, v_isMeta_4586_);
v___x_4612_ = lean_st_ref_get(v___y_4589_);
v_env_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc_ref(v_env_4613_);
lean_dec(v___x_4612_);
v___x_4614_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4615_ = lean_box(1);
v___x_4616_ = lean_box(0);
v___x_4617_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4607_, v___x_4614_, v_env_4613_, v___x_4615_, v___x_4616_);
v___x_4618_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_4617_, v_entry_4611_);
lean_dec(v___x_4617_);
if (v___x_4618_ == 0)
{
lean_object* v_toCold_4619_; lean_object* v_options_4620_; lean_object* v_inheritedTraceOptions_4621_; uint8_t v_hasTrace_4622_; lean_object* v___f_4623_; uint8_t v___x_4624_; lean_object* v___y_4626_; 
v_toCold_4619_ = lean_ctor_get(v___y_4588_, 0);
v_options_4620_ = lean_ctor_get(v_toCold_4619_, 2);
v_inheritedTraceOptions_4621_ = lean_ctor_get(v_toCold_4619_, 11);
v_hasTrace_4622_ = lean_ctor_get_uint8(v_options_4620_, sizeof(void*)*1);
v___f_4623_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4623_, 0, v___x_4614_);
lean_closure_set(v___f_4623_, 1, v_entry_4611_);
v___x_4624_ = 1;
if (v_hasTrace_4622_ == 0)
{
lean_dec(v_hint_4587_);
lean_dec(v_mod_4585_);
v___y_4626_ = v___y_4589_;
goto v___jp_4625_;
}
else
{
lean_object* v_cls_4644_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___x_4664_; uint8_t v___x_4665_; 
v_cls_4644_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4664_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4621_, v_options_4620_, v___x_4664_);
if (v___x_4665_ == 0)
{
lean_dec(v_hint_4587_);
lean_dec(v_mod_4585_);
v___y_4626_ = v___y_4589_;
goto v___jp_4625_;
}
else
{
lean_object* v___x_4666_; lean_object* v___y_4668_; 
v___x_4666_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_4610_ == 0)
{
lean_object* v___x_4675_; 
v___x_4675_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4668_ = v___x_4675_;
goto v___jp_4667_;
}
else
{
lean_object* v___x_4676_; 
v___x_4676_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4668_ = v___x_4676_;
goto v___jp_4667_;
}
v___jp_4667_:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_inc_ref(v___y_4668_);
v___x_4669_ = l_Lean_stringToMessageData(v___y_4668_);
v___x_4670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4666_);
lean_ctor_set(v___x_4670_, 1, v___x_4669_);
v___x_4671_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4670_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
if (v_isMeta_4586_ == 0)
{
lean_object* v___x_4673_; 
v___x_4673_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4651_ = v___x_4672_;
v___y_4652_ = v___x_4673_;
goto v___jp_4650_;
}
else
{
lean_object* v___x_4674_; 
v___x_4674_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4651_ = v___x_4672_;
v___y_4652_ = v___x_4674_;
goto v___jp_4650_;
}
}
}
v___jp_4645_:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___y_4646_);
lean_ctor_set(v___x_4648_, 1, v___y_4647_);
v___x_4649_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4644_, v___x_4648_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_dec_ref_known(v___x_4649_, 1);
v___y_4626_ = v___y_4589_;
goto v___jp_4625_;
}
else
{
lean_dec_ref(v___f_4623_);
return v___x_4649_;
}
}
v___jp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
lean_inc_ref(v___y_4652_);
v___x_4653_ = l_Lean_stringToMessageData(v___y_4652_);
v___x_4654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4654_, 0, v___y_4651_);
lean_ctor_set(v___x_4654_, 1, v___x_4653_);
v___x_4655_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4654_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
v___x_4657_ = l_Lean_MessageData_ofName(v_mod_4585_);
v___x_4658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4656_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
v___x_4659_ = l_Lean_Name_isAnonymous(v_hint_4587_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4661_ = l_Lean_MessageData_ofName(v_hint_4587_);
v___x_4662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4660_);
lean_ctor_set(v___x_4662_, 1, v___x_4661_);
v___y_4646_ = v___x_4658_;
v___y_4647_ = v___x_4662_;
goto v___jp_4645_;
}
else
{
lean_object* v___x_4663_; 
lean_dec(v_hint_4587_);
v___x_4663_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4646_ = v___x_4658_;
v___y_4647_ = v___x_4663_;
goto v___jp_4645_;
}
}
}
v___jp_4625_:
{
lean_object* v___x_4627_; lean_object* v_toEnvExtension_4628_; lean_object* v_env_4629_; lean_object* v_nextMacroScope_4630_; lean_object* v_ngen_4631_; lean_object* v_auxDeclNGen_4632_; lean_object* v_traceState_4633_; lean_object* v_recordedDeps_4634_; lean_object* v_messages_4635_; lean_object* v_infoState_4636_; lean_object* v_snapshotTasks_4637_; lean_object* v_asyncMode_4638_; uint8_t v_logWrites_4639_; lean_object* v___x_4640_; 
v___x_4627_ = lean_st_ref_take(v___y_4626_);
v_toEnvExtension_4628_ = lean_ctor_get(v___x_4614_, 0);
v_env_4629_ = lean_ctor_get(v___x_4627_, 0);
lean_inc_ref(v_env_4629_);
v_nextMacroScope_4630_ = lean_ctor_get(v___x_4627_, 1);
lean_inc(v_nextMacroScope_4630_);
v_ngen_4631_ = lean_ctor_get(v___x_4627_, 2);
lean_inc_ref(v_ngen_4631_);
v_auxDeclNGen_4632_ = lean_ctor_get(v___x_4627_, 3);
lean_inc_ref(v_auxDeclNGen_4632_);
v_traceState_4633_ = lean_ctor_get(v___x_4627_, 4);
lean_inc_ref(v_traceState_4633_);
v_recordedDeps_4634_ = lean_ctor_get(v___x_4627_, 6);
lean_inc_ref(v_recordedDeps_4634_);
v_messages_4635_ = lean_ctor_get(v___x_4627_, 7);
lean_inc_ref(v_messages_4635_);
v_infoState_4636_ = lean_ctor_get(v___x_4627_, 8);
lean_inc_ref(v_infoState_4636_);
v_snapshotTasks_4637_ = lean_ctor_get(v___x_4627_, 9);
lean_inc_ref(v_snapshotTasks_4637_);
lean_dec(v___x_4627_);
v_asyncMode_4638_ = lean_ctor_get(v_toEnvExtension_4628_, 2);
v_logWrites_4639_ = lean_ctor_get_uint8(v_toEnvExtension_4628_, sizeof(void*)*6);
v___x_4640_ = lean_box(0);
if (v_logWrites_4639_ == 0)
{
lean_object* v___x_4641_; 
lean_inc_ref(v_toEnvExtension_4628_);
v___x_4641_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4628_, v_env_4629_, v___f_4623_, v_asyncMode_4638_, v___x_4616_, v___x_4624_);
v___y_4592_ = v___x_4640_;
v___y_4593_ = v_infoState_4636_;
v___y_4594_ = v_snapshotTasks_4637_;
v___y_4595_ = v_recordedDeps_4634_;
v___y_4596_ = v_ngen_4631_;
v___y_4597_ = v_messages_4635_;
v___y_4598_ = v_traceState_4633_;
v___y_4599_ = v___y_4626_;
v___y_4600_ = v_nextMacroScope_4630_;
v___y_4601_ = v_auxDeclNGen_4632_;
v___y_4602_ = v___x_4641_;
goto v___jp_4591_;
}
else
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
lean_inc_ref_n(v_toEnvExtension_4628_, 2);
v___x_4642_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4628_, v_env_4629_);
lean_dec_ref(v_env_4629_);
v___x_4643_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4628_, v___x_4642_, v___f_4623_, v_asyncMode_4638_, v___x_4616_, v___x_4624_);
v___y_4592_ = v___x_4640_;
v___y_4593_ = v_infoState_4636_;
v___y_4594_ = v_snapshotTasks_4637_;
v___y_4595_ = v_recordedDeps_4634_;
v___y_4596_ = v_ngen_4631_;
v___y_4597_ = v_messages_4635_;
v___y_4598_ = v_traceState_4633_;
v___y_4599_ = v___y_4626_;
v___y_4600_ = v_nextMacroScope_4630_;
v___y_4601_ = v_auxDeclNGen_4632_;
v___y_4602_ = v___x_4643_;
goto v___jp_4591_;
}
}
}
else
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
lean_dec_ref_known(v_entry_4611_, 1);
lean_dec(v_hint_4587_);
lean_dec(v_mod_4585_);
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
return v___x_4678_;
}
v___jp_4591_:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4603_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___closed__1);
v___x_4604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4604_, 0, v___y_4602_);
lean_ctor_set(v___x_4604_, 1, v___y_4600_);
lean_ctor_set(v___x_4604_, 2, v___y_4596_);
lean_ctor_set(v___x_4604_, 3, v___y_4601_);
lean_ctor_set(v___x_4604_, 4, v___y_4598_);
lean_ctor_set(v___x_4604_, 5, v___x_4603_);
lean_ctor_set(v___x_4604_, 6, v___y_4595_);
lean_ctor_set(v___x_4604_, 7, v___y_4597_);
lean_ctor_set(v___x_4604_, 8, v___y_4593_);
lean_ctor_set(v___x_4604_, 9, v___y_4594_);
v___x_4605_ = lean_st_ref_put(v___y_4599_, v___x_4604_);
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v___y_4592_);
return v___x_4606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_4679_, lean_object* v_isMeta_4680_, lean_object* v_hint_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
uint8_t v_isMeta_boxed_4685_; lean_object* v_res_4686_; 
v_isMeta_boxed_4685_ = lean_unbox(v_isMeta_4680_);
v_res_4686_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_4679_, v_isMeta_boxed_4685_, v_hint_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_4687_, lean_object* v_declName_4688_, lean_object* v_as_4689_, size_t v_sz_4690_, size_t v_i_4691_, lean_object* v_b_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
uint8_t v___x_4696_; 
v___x_4696_ = lean_usize_dec_lt(v_i_4691_, v_sz_4690_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; 
lean_dec(v_declName_4688_);
v___x_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4697_, 0, v_b_4692_);
return v___x_4697_;
}
else
{
lean_object* v___x_4698_; lean_object* v_modules_4699_; lean_object* v___x_4700_; lean_object* v_a_4701_; lean_object* v___x_4702_; lean_object* v_toImport_4703_; lean_object* v_module_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; lean_object* v___x_4707_; 
v___x_4698_ = l_Lean_Environment_header(v___x_4687_);
v_modules_4699_ = lean_ctor_get(v___x_4698_, 3);
lean_inc_ref(v_modules_4699_);
lean_dec_ref(v___x_4698_);
v___x_4700_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4701_ = lean_array_uget_borrowed(v_as_4689_, v_i_4691_);
v___x_4702_ = lean_array_get(v___x_4700_, v_modules_4699_, v_a_4701_);
lean_dec_ref(v_modules_4699_);
v_toImport_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc_ref(v_toImport_4703_);
lean_dec(v___x_4702_);
v_module_4704_ = lean_ctor_get(v_toImport_4703_, 0);
lean_inc(v_module_4704_);
lean_dec_ref(v_toImport_4703_);
v___x_4705_ = lean_box(0);
v___x_4706_ = 0;
lean_inc(v_declName_4688_);
v___x_4707_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4704_, v___x_4706_, v_declName_4688_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4707_) == 0)
{
size_t v___x_4708_; size_t v___x_4709_; 
lean_dec_ref_known(v___x_4707_, 1);
v___x_4708_ = ((size_t)1ULL);
v___x_4709_ = lean_usize_add(v_i_4691_, v___x_4708_);
v_i_4691_ = v___x_4709_;
v_b_4692_ = v___x_4705_;
goto _start;
}
else
{
lean_dec(v_declName_4688_);
return v___x_4707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_4711_, lean_object* v_declName_4712_, lean_object* v_as_4713_, lean_object* v_sz_4714_, lean_object* v_i_4715_, lean_object* v_b_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
size_t v_sz_boxed_4720_; size_t v_i_boxed_4721_; lean_object* v_res_4722_; 
v_sz_boxed_4720_ = lean_unbox_usize(v_sz_4714_);
lean_dec(v_sz_4714_);
v_i_boxed_4721_ = lean_unbox_usize(v_i_4715_);
lean_dec(v_i_4715_);
v_res_4722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_4711_, v_declName_4712_, v_as_4713_, v_sz_boxed_4720_, v_i_boxed_4721_, v_b_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec_ref(v_as_4713_);
lean_dec_ref(v___x_4711_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_4723_, uint8_t v_isMeta_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v_env_4733_; lean_object* v___y_4735_; lean_object* v___x_4748_; 
v___x_4728_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4729_ = lean_st_ref_get(v___y_4726_);
v_env_4733_ = lean_ctor_get(v___x_4729_, 0);
lean_inc_ref(v_env_4733_);
lean_dec(v___x_4729_);
v___x_4748_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4733_, v_declName_4723_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_dec_ref(v_env_4733_);
lean_dec(v_declName_4723_);
goto v___jp_4730_;
}
else
{
lean_object* v_val_4749_; lean_object* v___x_4750_; lean_object* v_modules_4751_; lean_object* v___x_4752_; uint8_t v___x_4753_; 
v_val_4749_ = lean_ctor_get(v___x_4748_, 0);
lean_inc(v_val_4749_);
lean_dec_ref_known(v___x_4748_, 1);
v___x_4750_ = l_Lean_Environment_header(v_env_4733_);
v_modules_4751_ = lean_ctor_get(v___x_4750_, 3);
lean_inc_ref(v_modules_4751_);
lean_dec_ref(v___x_4750_);
v___x_4752_ = lean_array_get_size(v_modules_4751_);
v___x_4753_ = lean_nat_dec_lt(v_val_4749_, v___x_4752_);
if (v___x_4753_ == 0)
{
lean_dec_ref(v_modules_4751_);
lean_dec(v_val_4749_);
lean_dec_ref(v_env_4733_);
lean_dec(v_declName_4723_);
goto v___jp_4730_;
}
else
{
lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___y_4757_; 
v___x_4754_ = lean_array_fget(v_modules_4751_, v_val_4749_);
lean_dec(v_val_4749_);
lean_dec_ref(v_modules_4751_);
v___x_4755_ = lean_st_ref_get(v___y_4726_);
if (v_isMeta_4724_ == 0)
{
lean_dec(v___x_4755_);
v___y_4757_ = v_isMeta_4724_;
goto v___jp_4756_;
}
else
{
lean_object* v_env_4768_; uint8_t v___x_4769_; 
v_env_4768_ = lean_ctor_get(v___x_4755_, 0);
lean_inc_ref(v_env_4768_);
lean_dec(v___x_4755_);
lean_inc(v_declName_4723_);
v___x_4769_ = l_Lean_isMarkedMeta(v_env_4768_, v_declName_4723_);
if (v___x_4769_ == 0)
{
v___y_4757_ = v_isMeta_4724_;
goto v___jp_4756_;
}
else
{
uint8_t v___x_4770_; 
v___x_4770_ = 0;
v___y_4757_ = v___x_4770_;
goto v___jp_4756_;
}
}
v___jp_4756_:
{
lean_object* v_toImport_4758_; lean_object* v_module_4759_; lean_object* v___x_4760_; 
v_toImport_4758_ = lean_ctor_get(v___x_4754_, 0);
lean_inc_ref(v_toImport_4758_);
lean_dec(v___x_4754_);
v_module_4759_ = lean_ctor_get(v_toImport_4758_, 0);
lean_inc(v_module_4759_);
lean_dec_ref(v_toImport_4758_);
lean_inc(v_declName_4723_);
v___x_4760_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4759_, v___y_4757_, v_declName_4723_, v___y_4725_, v___y_4726_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
lean_dec_ref_known(v___x_4760_, 1);
v___x_4761_ = l_Lean_indirectModUseExt;
v___x_4762_ = lean_box(1);
v___x_4763_ = lean_box(0);
lean_inc_ref(v_env_4733_);
v___x_4764_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4728_, v___x_4761_, v_env_4733_, v___x_4762_, v___x_4763_);
v___x_4765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4764_, v_declName_4723_);
lean_dec(v___x_4764_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v___x_4766_; 
v___x_4766_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4735_ = v___x_4766_;
goto v___jp_4734_;
}
else
{
lean_object* v_val_4767_; 
v_val_4767_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_val_4767_);
lean_dec_ref_known(v___x_4765_, 1);
v___y_4735_ = v_val_4767_;
goto v___jp_4734_;
}
}
else
{
lean_dec_ref(v_env_4733_);
lean_dec(v_declName_4723_);
return v___x_4760_;
}
}
}
}
v___jp_4730_:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = lean_box(0);
v___x_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4731_);
return v___x_4732_;
}
v___jp_4734_:
{
lean_object* v___x_4736_; size_t v_sz_4737_; size_t v___x_4738_; lean_object* v___x_4739_; 
v___x_4736_ = lean_box(0);
v_sz_4737_ = lean_array_size(v___y_4735_);
v___x_4738_ = ((size_t)0ULL);
v___x_4739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_4733_, v_declName_4723_, v___y_4735_, v_sz_4737_, v___x_4738_, v___x_4736_, v___y_4725_, v___y_4726_);
lean_dec_ref(v___y_4735_);
lean_dec_ref(v_env_4733_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4746_; 
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4746_ == 0)
{
lean_object* v_unused_4747_; 
v_unused_4747_ = lean_ctor_get(v___x_4739_, 0);
lean_dec(v_unused_4747_);
v___x_4741_ = v___x_4739_;
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
else
{
lean_dec(v___x_4739_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 0, v___x_4736_);
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4736_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
else
{
return v___x_4739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_4771_, lean_object* v_isMeta_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
uint8_t v_isMeta_boxed_4776_; lean_object* v_res_4777_; 
v_isMeta_boxed_4776_ = lean_unbox(v_isMeta_4772_);
v_res_4777_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_4771_, v_isMeta_boxed_4776_, v___y_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4782_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4783_ = lean_st_ref_get(v___x_4782_);
v___x_4784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4783_, v_attrName_4778_);
lean_dec(v___x_4783_);
if (lean_obj_tag(v___x_4784_) == 1)
{
lean_object* v_val_4785_; lean_object* v_ext_4786_; lean_object* v_name_4787_; uint8_t v___x_4788_; lean_object* v___x_4789_; 
v_val_4785_ = lean_ctor_get(v___x_4784_, 0);
v_ext_4786_ = lean_ctor_get(v_val_4785_, 1);
v_name_4787_ = lean_ctor_get(v_ext_4786_, 1);
v___x_4788_ = 1;
lean_inc(v_name_4787_);
v___x_4789_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_4787_, v___x_4788_, v_a_4779_, v_a_4780_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4796_; 
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; 
v_unused_4797_ = lean_ctor_get(v___x_4789_, 0);
lean_dec(v_unused_4797_);
v___x_4791_ = v___x_4789_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_dec(v___x_4789_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4784_);
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4784_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec_ref_known(v___x_4784_, 1);
v_a_4798_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4789_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4789_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
else
{
lean_object* v___x_4806_; 
v___x_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4784_);
return v___x_4806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_4807_, v_a_4808_, v_a_4809_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_attrName_4807_);
return v_res_4811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_4813_, lean_object* v_x_4814_){
_start:
{
if (lean_obj_tag(v_x_4814_) == 0)
{
return v_x_4813_;
}
else
{
lean_object* v_key_4815_; lean_object* v_value_4816_; lean_object* v_tail_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4843_; 
v_key_4815_ = lean_ctor_get(v_x_4814_, 0);
v_value_4816_ = lean_ctor_get(v_x_4814_, 1);
v_tail_4817_ = lean_ctor_get(v_x_4814_, 2);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_x_4814_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4819_ = v_x_4814_;
v_isShared_4820_ = v_isSharedCheck_4843_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_tail_4817_);
lean_inc(v_value_4816_);
lean_inc(v_key_4815_);
lean_dec(v_x_4814_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4843_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; uint64_t v___y_4823_; 
v___x_4821_ = lean_array_get_size(v_x_4813_);
if (lean_obj_tag(v_key_4815_) == 0)
{
uint64_t v___x_4841_; 
v___x_4841_ = 1723ULL;
v___y_4823_ = v___x_4841_;
goto v___jp_4822_;
}
else
{
uint64_t v_hash_4842_; 
v_hash_4842_ = lean_ctor_get_uint64(v_key_4815_, sizeof(void*)*2);
v___y_4823_ = v_hash_4842_;
goto v___jp_4822_;
}
v___jp_4822_:
{
uint64_t v___x_4824_; uint64_t v___x_4825_; uint64_t v_fold_4826_; uint64_t v___x_4827_; uint64_t v___x_4828_; uint64_t v___x_4829_; size_t v___x_4830_; size_t v___x_4831_; size_t v___x_4832_; size_t v___x_4833_; size_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___x_4824_ = 32ULL;
v___x_4825_ = lean_uint64_shift_right(v___y_4823_, v___x_4824_);
v_fold_4826_ = lean_uint64_xor(v___y_4823_, v___x_4825_);
v___x_4827_ = 16ULL;
v___x_4828_ = lean_uint64_shift_right(v_fold_4826_, v___x_4827_);
v___x_4829_ = lean_uint64_xor(v_fold_4826_, v___x_4828_);
v___x_4830_ = lean_uint64_to_usize(v___x_4829_);
v___x_4831_ = lean_usize_of_nat(v___x_4821_);
v___x_4832_ = ((size_t)1ULL);
v___x_4833_ = lean_usize_sub(v___x_4831_, v___x_4832_);
v___x_4834_ = lean_usize_land(v___x_4830_, v___x_4833_);
v___x_4835_ = lean_array_uget_borrowed(v_x_4813_, v___x_4834_);
lean_inc(v___x_4835_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 2, v___x_4835_);
v___x_4837_ = v___x_4819_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_key_4815_);
lean_ctor_set(v_reuseFailAlloc_4840_, 1, v_value_4816_);
lean_ctor_set(v_reuseFailAlloc_4840_, 2, v___x_4835_);
v___x_4837_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
lean_object* v___x_4838_; 
v___x_4838_ = lean_array_uset(v_x_4813_, v___x_4834_, v___x_4837_);
v_x_4813_ = v___x_4838_;
v_x_4814_ = v_tail_4817_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4844_, lean_object* v_source_4845_, lean_object* v_target_4846_){
_start:
{
lean_object* v___x_4847_; uint8_t v___x_4848_; 
v___x_4847_ = lean_array_get_size(v_source_4845_);
v___x_4848_ = lean_nat_dec_lt(v_i_4844_, v___x_4847_);
if (v___x_4848_ == 0)
{
lean_dec_ref(v_source_4845_);
lean_dec(v_i_4844_);
return v_target_4846_;
}
else
{
lean_object* v_es_4849_; lean_object* v___x_4850_; lean_object* v_source_4851_; lean_object* v_target_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v_es_4849_ = lean_array_fget(v_source_4845_, v_i_4844_);
v___x_4850_ = lean_box(0);
v_source_4851_ = lean_array_fset(v_source_4845_, v_i_4844_, v___x_4850_);
v_target_4852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_4846_, v_es_4849_);
v___x_4853_ = lean_unsigned_to_nat(1u);
v___x_4854_ = lean_nat_add(v_i_4844_, v___x_4853_);
lean_dec(v_i_4844_);
v_i_4844_ = v___x_4854_;
v_source_4845_ = v_source_4851_;
v_target_4846_ = v_target_4852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_4856_){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v_nbuckets_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4857_ = lean_array_get_size(v_data_4856_);
v___x_4858_ = lean_unsigned_to_nat(2u);
v_nbuckets_4859_ = lean_nat_mul(v___x_4857_, v___x_4858_);
v___x_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = lean_box(0);
v___x_4862_ = lean_mk_array(v_nbuckets_4859_, v___x_4861_);
v___x_4863_ = lean_array_propagate_mark(v_data_4856_, v___x_4862_);
v___x_4864_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_4860_, v_data_4856_, v___x_4863_);
return v___x_4864_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_4865_, lean_object* v_x_4866_){
_start:
{
if (lean_obj_tag(v_x_4866_) == 0)
{
uint8_t v___x_4867_; 
v___x_4867_ = 0;
return v___x_4867_;
}
else
{
lean_object* v_key_4868_; lean_object* v_tail_4869_; uint8_t v___x_4870_; 
v_key_4868_ = lean_ctor_get(v_x_4866_, 0);
v_tail_4869_ = lean_ctor_get(v_x_4866_, 2);
v___x_4870_ = lean_name_eq(v_key_4868_, v_a_4865_);
if (v___x_4870_ == 0)
{
v_x_4866_ = v_tail_4869_;
goto _start;
}
else
{
return v___x_4870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_4872_, lean_object* v_x_4873_){
_start:
{
uint8_t v_res_4874_; lean_object* v_r_4875_; 
v_res_4874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4872_, v_x_4873_);
lean_dec(v_x_4873_);
lean_dec(v_a_4872_);
v_r_4875_ = lean_box(v_res_4874_);
return v_r_4875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_4876_, lean_object* v_b_4877_, lean_object* v_x_4878_){
_start:
{
if (lean_obj_tag(v_x_4878_) == 0)
{
lean_dec(v_b_4877_);
lean_dec(v_a_4876_);
return v_x_4878_;
}
else
{
lean_object* v_key_4879_; lean_object* v_value_4880_; lean_object* v_tail_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4893_; 
v_key_4879_ = lean_ctor_get(v_x_4878_, 0);
v_value_4880_ = lean_ctor_get(v_x_4878_, 1);
v_tail_4881_ = lean_ctor_get(v_x_4878_, 2);
v_isSharedCheck_4893_ = !lean_is_exclusive(v_x_4878_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4883_ = v_x_4878_;
v_isShared_4884_ = v_isSharedCheck_4893_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_tail_4881_);
lean_inc(v_value_4880_);
lean_inc(v_key_4879_);
lean_dec(v_x_4878_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4893_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
uint8_t v___x_4885_; 
v___x_4885_ = lean_name_eq(v_key_4879_, v_a_4876_);
if (v___x_4885_ == 0)
{
lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4886_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4876_, v_b_4877_, v_tail_4881_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 2, v___x_4886_);
v___x_4888_ = v___x_4883_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_key_4879_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_value_4880_);
lean_ctor_set(v_reuseFailAlloc_4889_, 2, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
else
{
lean_object* v___x_4891_; 
lean_dec(v_value_4880_);
lean_dec(v_key_4879_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 1, v_b_4877_);
lean_ctor_set(v___x_4883_, 0, v_a_4876_);
v___x_4891_ = v___x_4883_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4876_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_b_4877_);
lean_ctor_set(v_reuseFailAlloc_4892_, 2, v_tail_4881_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_4894_, lean_object* v_a_4895_, lean_object* v_b_4896_){
_start:
{
lean_object* v_size_4897_; lean_object* v_buckets_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4944_; 
v_size_4897_ = lean_ctor_get(v_m_4894_, 0);
v_buckets_4898_ = lean_ctor_get(v_m_4894_, 1);
v_isSharedCheck_4944_ = !lean_is_exclusive(v_m_4894_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4900_ = v_m_4894_;
v_isShared_4901_ = v_isSharedCheck_4944_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_buckets_4898_);
lean_inc(v_size_4897_);
lean_dec(v_m_4894_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4944_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4902_; uint64_t v___y_4904_; 
v___x_4902_ = lean_array_get_size(v_buckets_4898_);
if (lean_obj_tag(v_a_4895_) == 0)
{
uint64_t v___x_4942_; 
v___x_4942_ = 1723ULL;
v___y_4904_ = v___x_4942_;
goto v___jp_4903_;
}
else
{
uint64_t v_hash_4943_; 
v_hash_4943_ = lean_ctor_get_uint64(v_a_4895_, sizeof(void*)*2);
v___y_4904_ = v_hash_4943_;
goto v___jp_4903_;
}
v___jp_4903_:
{
uint64_t v___x_4905_; uint64_t v___x_4906_; uint64_t v_fold_4907_; uint64_t v___x_4908_; uint64_t v___x_4909_; uint64_t v___x_4910_; size_t v___x_4911_; size_t v___x_4912_; size_t v___x_4913_; size_t v___x_4914_; size_t v___x_4915_; lean_object* v_bkt_4916_; uint8_t v___x_4917_; 
v___x_4905_ = 32ULL;
v___x_4906_ = lean_uint64_shift_right(v___y_4904_, v___x_4905_);
v_fold_4907_ = lean_uint64_xor(v___y_4904_, v___x_4906_);
v___x_4908_ = 16ULL;
v___x_4909_ = lean_uint64_shift_right(v_fold_4907_, v___x_4908_);
v___x_4910_ = lean_uint64_xor(v_fold_4907_, v___x_4909_);
v___x_4911_ = lean_uint64_to_usize(v___x_4910_);
v___x_4912_ = lean_usize_of_nat(v___x_4902_);
v___x_4913_ = ((size_t)1ULL);
v___x_4914_ = lean_usize_sub(v___x_4912_, v___x_4913_);
v___x_4915_ = lean_usize_land(v___x_4911_, v___x_4914_);
v_bkt_4916_ = lean_array_uget_borrowed(v_buckets_4898_, v___x_4915_);
v___x_4917_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4895_, v_bkt_4916_);
if (v___x_4917_ == 0)
{
lean_object* v___x_4918_; lean_object* v_size_x27_4919_; lean_object* v___x_4920_; lean_object* v_buckets_x27_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
v___x_4918_ = lean_unsigned_to_nat(1u);
v_size_x27_4919_ = lean_nat_add(v_size_4897_, v___x_4918_);
lean_dec(v_size_4897_);
lean_inc(v_bkt_4916_);
v___x_4920_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4920_, 0, v_a_4895_);
lean_ctor_set(v___x_4920_, 1, v_b_4896_);
lean_ctor_set(v___x_4920_, 2, v_bkt_4916_);
v_buckets_x27_4921_ = lean_array_uset(v_buckets_4898_, v___x_4915_, v___x_4920_);
v___x_4922_ = lean_unsigned_to_nat(4u);
v___x_4923_ = lean_nat_mul(v_size_x27_4919_, v___x_4922_);
v___x_4924_ = lean_unsigned_to_nat(3u);
v___x_4925_ = lean_nat_div(v___x_4923_, v___x_4924_);
lean_dec(v___x_4923_);
v___x_4926_ = lean_array_get_size(v_buckets_x27_4921_);
v___x_4927_ = lean_nat_dec_le(v___x_4925_, v___x_4926_);
lean_dec(v___x_4925_);
if (v___x_4927_ == 0)
{
lean_object* v_val_4928_; lean_object* v___x_4930_; 
v_val_4928_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_4921_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v_val_4928_);
lean_ctor_set(v___x_4900_, 0, v_size_x27_4919_);
v___x_4930_ = v___x_4900_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_size_x27_4919_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_val_4928_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
else
{
lean_object* v___x_4933_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v_buckets_x27_4921_);
lean_ctor_set(v___x_4900_, 0, v_size_x27_4919_);
v___x_4933_ = v___x_4900_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_size_x27_4919_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_buckets_x27_4921_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
else
{
lean_object* v___x_4935_; lean_object* v_buckets_x27_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4940_; 
lean_inc(v_bkt_4916_);
v___x_4935_ = lean_box(0);
v_buckets_x27_4936_ = lean_array_uset(v_buckets_4898_, v___x_4915_, v___x_4935_);
v___x_4937_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4895_, v_b_4896_, v_bkt_4916_);
v___x_4938_ = lean_array_uset(v_buckets_x27_4936_, v___x_4915_, v___x_4937_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v___x_4938_);
v___x_4940_ = v___x_4900_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_size_4897_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_4945_, lean_object* v_ref_4946_){
_start:
{
lean_object* v___x_4948_; 
lean_inc(v_ref_4946_);
v___x_4948_ = l_Lean_Meta_Grind_mkExtension(v_ref_4946_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v_a_4949_; uint8_t v___x_4950_; uint8_t v___x_4951_; lean_object* v___x_4952_; 
v_a_4949_ = lean_ctor_get(v___x_4948_, 0);
lean_inc_n(v_a_4949_, 2);
lean_dec_ref_known(v___x_4948_, 1);
v___x_4950_ = 0;
v___x_4951_ = 1;
lean_inc(v_ref_4946_);
lean_inc(v_attrName_4945_);
v___x_4952_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4945_, v___x_4950_, v___x_4951_, v_a_4949_, v_ref_4946_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v___x_4953_; 
lean_dec_ref_known(v___x_4952_, 1);
lean_inc(v_ref_4946_);
lean_inc(v_a_4949_);
lean_inc(v_attrName_4945_);
v___x_4953_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4945_, v___x_4950_, v___x_4950_, v_a_4949_, v_ref_4946_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4954_; 
lean_dec_ref_known(v___x_4953_, 1);
lean_inc(v_ref_4946_);
lean_inc(v_a_4949_);
lean_inc(v_attrName_4945_);
v___x_4954_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4945_, v___x_4951_, v___x_4951_, v_a_4949_, v_ref_4946_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4955_; 
lean_dec_ref_known(v___x_4954_, 1);
lean_inc(v_a_4949_);
lean_inc(v_attrName_4945_);
v___x_4955_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4945_, v___x_4951_, v___x_4950_, v_a_4949_, v_ref_4946_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4966_; 
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4966_ == 0)
{
lean_object* v_unused_4967_; 
v_unused_4967_ = lean_ctor_get(v___x_4955_, 0);
lean_dec(v_unused_4967_);
v___x_4957_ = v___x_4955_;
v_isShared_4958_ = v_isSharedCheck_4966_;
goto v_resetjp_4956_;
}
else
{
lean_dec(v___x_4955_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4966_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4964_; 
v___x_4959_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4960_ = lean_st_ref_take(v___x_4959_);
lean_inc(v_a_4949_);
v___x_4961_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4960_, v_attrName_4945_, v_a_4949_);
v___x_4962_ = lean_st_ref_put(v___x_4959_, v___x_4961_);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 0, v_a_4949_);
v___x_4964_ = v___x_4957_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4949_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
else
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_dec(v_a_4949_);
lean_dec(v_attrName_4945_);
v_a_4968_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4955_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4955_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec(v_a_4949_);
lean_dec(v_ref_4946_);
lean_dec(v_attrName_4945_);
v_a_4976_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4954_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4954_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
lean_dec(v_a_4949_);
lean_dec(v_ref_4946_);
lean_dec(v_attrName_4945_);
v_a_4984_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4953_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4953_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec(v_a_4949_);
lean_dec(v_ref_4946_);
lean_dec(v_attrName_4945_);
v_a_4992_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4952_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4952_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
else
{
lean_dec(v_ref_4946_);
lean_dec(v_attrName_4945_);
return v___x_4948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_5000_, lean_object* v_ref_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_Meta_Grind_registerAttr(v_attrName_5000_, v_ref_5001_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_5004_, lean_object* v_m_5005_, lean_object* v_a_5006_, lean_object* v_b_5007_){
_start:
{
lean_object* v___x_5008_; 
v___x_5008_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_5005_, v_a_5006_, v_b_5007_);
return v___x_5008_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_5009_, lean_object* v_a_5010_, lean_object* v_x_5011_){
_start:
{
uint8_t v___x_5012_; 
v___x_5012_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_5010_, v_x_5011_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5013_, lean_object* v_a_5014_, lean_object* v_x_5015_){
_start:
{
uint8_t v_res_5016_; lean_object* v_r_5017_; 
v_res_5016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_5013_, v_a_5014_, v_x_5015_);
lean_dec(v_x_5015_);
lean_dec(v_a_5014_);
v_r_5017_ = lean_box(v_res_5016_);
return v_r_5017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_5018_, lean_object* v_data_5019_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_5019_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_5021_, lean_object* v_a_5022_, lean_object* v_b_5023_, lean_object* v_x_5024_){
_start:
{
lean_object* v___x_5025_; 
v___x_5025_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_5022_, v_b_5023_, v_x_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5026_, lean_object* v_i_5027_, lean_object* v_source_5028_, lean_object* v_target_5029_){
_start:
{
lean_object* v___x_5030_; 
v___x_5030_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_5027_, v_source_5028_, v_target_5029_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5031_, lean_object* v_x_5032_, lean_object* v_x_5033_){
_start:
{
lean_object* v___x_5034_; 
v___x_5034_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5032_, v_x_5033_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_5042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_5043_ = l_Lean_Meta_Grind_registerAttr(v___x_5041_, v___x_5042_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5058_ = l_Lean_Meta_Grind_registerAttr(v___x_5056_, v___x_5057_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v_env_5066_; lean_object* v___x_5067_; lean_object* v_ext_5068_; lean_object* v_toEnvExtension_5069_; lean_object* v_asyncMode_5070_; uint8_t v___x_5071_; lean_object* v___x_5072_; lean_object* v_casesTypes_5073_; uint8_t v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5064_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_5065_ = lean_st_ref_get(v_a_5062_);
v_env_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc_ref(v_env_5066_);
lean_dec(v___x_5065_);
v___x_5067_ = l_Lean_Meta_Grind_grindExt;
v_ext_5068_ = lean_ctor_get(v___x_5067_, 1);
v_toEnvExtension_5069_ = lean_ctor_get(v_ext_5068_, 0);
v_asyncMode_5070_ = lean_ctor_get(v_toEnvExtension_5069_, 2);
v___x_5071_ = 0;
v___x_5072_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5064_, v___x_5067_, v_env_5066_, v_asyncMode_5070_, v___x_5071_);
v_casesTypes_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc_ref(v_casesTypes_5073_);
lean_dec(v___x_5072_);
v___x_5074_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_5073_, v_declName_5061_);
lean_dec_ref(v_casesTypes_5073_);
v___x_5075_ = lean_box(v___x_5074_);
v___x_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5075_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5077_, v_a_5078_);
lean_dec(v_a_5078_);
lean_dec(v_declName_5077_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_){
_start:
{
lean_object* v___x_5085_; 
v___x_5085_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5081_, v_a_5083_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_5086_, v_a_5087_, v_a_5088_);
lean_dec(v_a_5088_);
lean_dec_ref(v_a_5087_);
lean_dec(v_declName_5086_);
return v_res_5090_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default = _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default);
l_Lean_Meta_Grind_instInhabitedNormSymTheorems = _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymTheorems);
l_Lean_Meta_Grind_instInhabitedNormSymEntry_default = _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymEntry_default);
l_Lean_Meta_Grind_instInhabitedNormSymEntry = _init_l_Lean_Meta_Grind_instInhabitedNormSymEntry();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedNormSymEntry);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2087691235____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normSymExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normSymExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_grindExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_grindExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_liaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_liaExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1 = _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1);
l_Lean_Meta_Grind_registerAttr___auto__1 = _init_l_Lean_Meta_Grind_registerAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
