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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0(lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___closed__0);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
return v_res_497_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1___redArg();
return v___x_502_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__0);
v___x_504_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
v___x_505_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_503_);
lean_ctor_set(v___x_505_, 3, v___x_503_);
lean_ctor_set(v___x_505_, 4, v___x_503_);
lean_ctor_set(v___x_505_, 5, v___x_503_);
lean_ctor_set(v___x_505_, 6, v___x_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(lean_object* v_ext_506_, lean_object* v_b_507_, uint8_t v_kind_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_toCold_513_; lean_object* v_currNamespace_514_; lean_object* v___x_515_; lean_object* v_env_516_; lean_object* v_nextMacroScope_517_; lean_object* v_ngen_518_; lean_object* v_auxDeclNGen_519_; lean_object* v_traceState_520_; lean_object* v_recordedDeps_521_; lean_object* v_messages_522_; lean_object* v_infoState_523_; lean_object* v_snapshotTasks_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_551_; 
v_toCold_513_ = lean_ctor_get(v___y_510_, 0);
v_currNamespace_514_ = lean_ctor_get(v_toCold_513_, 4);
v___x_515_ = lean_st_ref_take(v___y_511_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
v_nextMacroScope_517_ = lean_ctor_get(v___x_515_, 1);
v_ngen_518_ = lean_ctor_get(v___x_515_, 2);
v_auxDeclNGen_519_ = lean_ctor_get(v___x_515_, 3);
v_traceState_520_ = lean_ctor_get(v___x_515_, 4);
v_recordedDeps_521_ = lean_ctor_get(v___x_515_, 6);
v_messages_522_ = lean_ctor_get(v___x_515_, 7);
v_infoState_523_ = lean_ctor_get(v___x_515_, 8);
v_snapshotTasks_524_ = lean_ctor_get(v___x_515_, 9);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_515_, 5);
lean_dec(v_unused_552_);
v___x_526_ = v___x_515_;
v_isShared_527_ = v_isSharedCheck_551_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snapshotTasks_524_);
lean_inc(v_infoState_523_);
lean_inc(v_messages_522_);
lean_inc(v_recordedDeps_521_);
lean_inc(v_traceState_520_);
lean_inc(v_auxDeclNGen_519_);
lean_inc(v_ngen_518_);
lean_inc(v_nextMacroScope_517_);
lean_inc(v_env_516_);
lean_dec(v___x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_551_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc(v_currNamespace_514_);
v___x_528_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_516_, v_ext_506_, v_b_507_, v_kind_508_, v_currNamespace_514_);
v___x_529_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 5, v___x_529_);
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_nextMacroScope_517_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_ngen_518_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_auxDeclNGen_519_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_traceState_520_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_recordedDeps_521_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_messages_522_);
lean_ctor_set(v_reuseFailAlloc_550_, 8, v_infoState_523_);
lean_ctor_set(v_reuseFailAlloc_550_, 9, v_snapshotTasks_524_);
v___x_531_ = v_reuseFailAlloc_550_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_mctx_534_; lean_object* v_zetaDeltaFVarIds_535_; lean_object* v_postponed_536_; lean_object* v_diag_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
v___x_532_ = lean_st_ref_put(v___y_511_, v___x_531_);
v___x_533_ = lean_st_ref_take(v___y_509_);
v_mctx_534_ = lean_ctor_get(v___x_533_, 0);
v_zetaDeltaFVarIds_535_ = lean_ctor_get(v___x_533_, 2);
v_postponed_536_ = lean_ctor_get(v___x_533_, 3);
v_diag_537_ = lean_ctor_get(v___x_533_, 4);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_533_, 1);
lean_dec(v_unused_549_);
v___x_539_ = v___x_533_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_diag_537_);
lean_inc(v_postponed_536_);
lean_inc(v_zetaDeltaFVarIds_535_);
lean_inc(v_mctx_534_);
lean_dec(v___x_533_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_mctx_534_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_zetaDeltaFVarIds_535_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_postponed_536_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_diag_537_);
v___x_544_ = v_reuseFailAlloc_547_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_st_ref_put(v___y_509_, v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_541_);
return v___x_546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___boxed(lean_object* v_ext_553_, lean_object* v_b_554_, lean_object* v_kind_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v_kind_boxed_560_; lean_object* v_res_561_; 
v_kind_boxed_560_ = lean_unbox(v_kind_555_);
v_res_561_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_553_, v_b_554_, v_kind_boxed_560_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(uint8_t v_attrKind_562_, uint8_t v_post_563_, lean_object* v_as_564_, size_t v_sz_565_, size_t v_i_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_a_574_; uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_lt(v_i_566_, v_sz_565_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v_b_567_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_580_ = lean_box(0);
v_a_581_ = lean_array_uget_borrowed(v_as_564_, v_i_566_);
v___x_582_ = l_Lean_Meta_Grind_normExt;
lean_inc(v_a_581_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_a_581_);
v___x_584_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_582_, v___x_583_, v_attrKind_562_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_626_; 
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_627_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_626_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_626_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; 
lean_inc(v_a_581_);
v___x_588_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f(v_a_581_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
if (lean_obj_tag(v_a_589_) == 1)
{
lean_object* v_val_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_617_; 
v_val_590_ = lean_ctor_get(v_a_589_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_589_);
if (v_isSharedCheck_617_ == 0)
{
v___x_592_ = v_a_589_;
v_isShared_593_ = v_isSharedCheck_617_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_val_590_);
lean_dec(v_a_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_617_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___y_596_; 
v___x_594_ = l_Lean_Meta_Grind_normSymExt;
if (v_post_563_ == 0)
{
lean_object* v___x_612_; 
lean_inc(v_val_590_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_val_590_);
v___x_612_ = v___x_586_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_val_590_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v___y_596_ = v___x_612_;
goto v___jp_595_;
}
}
else
{
lean_object* v___x_615_; 
lean_inc(v_val_590_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 1);
lean_ctor_set(v___x_586_, 0, v_val_590_);
v___x_615_ = v___x_586_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_val_590_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v___y_596_ = v___x_615_;
goto v___jp_595_;
}
}
v___jp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_594_, v___y_596_, v_attrKind_562_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_609_; 
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_610_);
v___x_599_ = v___x_597_;
v_isShared_600_ = v_isSharedCheck_609_;
goto v_resetjp_598_;
}
else
{
lean_dec(v___x_597_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_609_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
if (v_post_563_ == 0)
{
lean_del_object(v___x_599_);
lean_del_object(v___x_592_);
lean_dec(v_val_590_);
v_a_574_ = v___x_580_;
goto v___jp_573_;
}
else
{
uint8_t v_rfl_601_; 
v_rfl_601_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*5 + 2);
if (v_rfl_601_ == 0)
{
lean_del_object(v___x_599_);
lean_del_object(v___x_592_);
lean_dec(v_val_590_);
v_a_574_ = v___x_580_;
goto v___jp_573_;
}
else
{
lean_object* v___x_603_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_val_590_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_val_590_);
v___x_603_ = v_reuseFailAlloc_608_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 2);
lean_ctor_set(v___x_592_, 0, v___x_603_);
v___x_605_ = v___x_592_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_594_, v___x_605_, v_attrKind_562_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_dec_ref_known(v___x_606_, 1);
v_a_574_ = v___x_580_;
goto v___jp_573_;
}
else
{
return v___x_606_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_592_);
lean_dec(v_val_590_);
return v___x_597_;
}
}
}
}
else
{
lean_dec(v_a_589_);
lean_del_object(v___x_586_);
v_a_574_ = v___x_580_;
goto v___jp_573_;
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_del_object(v___x_586_);
v_a_618_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_588_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_588_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
else
{
return v___x_584_;
}
}
v___jp_573_:
{
size_t v___x_575_; size_t v___x_576_; 
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_566_, v___x_575_);
v_i_566_ = v___x_576_;
v_b_567_ = v_a_574_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2___boxed(lean_object* v_attrKind_628_, lean_object* v_post_629_, lean_object* v_as_630_, lean_object* v_sz_631_, lean_object* v_i_632_, lean_object* v_b_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v_attrKind_boxed_639_; uint8_t v_post_boxed_640_; size_t v_sz_boxed_641_; size_t v_i_boxed_642_; lean_object* v_res_643_; 
v_attrKind_boxed_639_ = lean_unbox(v_attrKind_628_);
v_post_boxed_640_ = lean_unbox(v_post_629_);
v_sz_boxed_641_ = lean_unbox_usize(v_sz_631_);
lean_dec(v_sz_631_);
v_i_boxed_642_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_boxed_639_, v_post_boxed_640_, v_as_630_, v_sz_boxed_641_, v_i_boxed_642_, v_b_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v_as_630_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(lean_object* v___y_644_, uint8_t v_isExporting_645_, lean_object* v___x_646_, lean_object* v___y_647_, lean_object* v___x_648_, lean_object* v_a_x3f_649_){
_start:
{
lean_object* v___x_651_; lean_object* v_env_652_; lean_object* v_nextMacroScope_653_; lean_object* v_ngen_654_; lean_object* v_auxDeclNGen_655_; lean_object* v_traceState_656_; lean_object* v_recordedDeps_657_; lean_object* v_messages_658_; lean_object* v_infoState_659_; lean_object* v_snapshotTasks_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_685_; 
v___x_651_ = lean_st_ref_take(v___y_644_);
v_env_652_ = lean_ctor_get(v___x_651_, 0);
v_nextMacroScope_653_ = lean_ctor_get(v___x_651_, 1);
v_ngen_654_ = lean_ctor_get(v___x_651_, 2);
v_auxDeclNGen_655_ = lean_ctor_get(v___x_651_, 3);
v_traceState_656_ = lean_ctor_get(v___x_651_, 4);
v_recordedDeps_657_ = lean_ctor_get(v___x_651_, 6);
v_messages_658_ = lean_ctor_get(v___x_651_, 7);
v_infoState_659_ = lean_ctor_get(v___x_651_, 8);
v_snapshotTasks_660_ = lean_ctor_get(v___x_651_, 9);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v___x_651_, 5);
lean_dec(v_unused_686_);
v___x_662_ = v___x_651_;
v_isShared_663_ = v_isSharedCheck_685_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snapshotTasks_660_);
lean_inc(v_infoState_659_);
lean_inc(v_messages_658_);
lean_inc(v_recordedDeps_657_);
lean_inc(v_traceState_656_);
lean_inc(v_auxDeclNGen_655_);
lean_inc(v_ngen_654_);
lean_inc(v_nextMacroScope_653_);
lean_inc(v_env_652_);
lean_dec(v___x_651_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_685_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = l_Lean_Environment_setExporting(v_env_652_, v_isExporting_645_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 5, v___x_646_);
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_nextMacroScope_653_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_ngen_654_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_auxDeclNGen_655_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_traceState_656_);
lean_ctor_set(v_reuseFailAlloc_684_, 5, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_684_, 6, v_recordedDeps_657_);
lean_ctor_set(v_reuseFailAlloc_684_, 7, v_messages_658_);
lean_ctor_set(v_reuseFailAlloc_684_, 8, v_infoState_659_);
lean_ctor_set(v_reuseFailAlloc_684_, 9, v_snapshotTasks_660_);
v___x_666_ = v_reuseFailAlloc_684_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_mctx_669_; lean_object* v_zetaDeltaFVarIds_670_; lean_object* v_postponed_671_; lean_object* v_diag_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_682_; 
v___x_667_ = lean_st_ref_put(v___y_644_, v___x_666_);
v___x_668_ = lean_st_ref_take(v___y_647_);
v_mctx_669_ = lean_ctor_get(v___x_668_, 0);
v_zetaDeltaFVarIds_670_ = lean_ctor_get(v___x_668_, 2);
v_postponed_671_ = lean_ctor_get(v___x_668_, 3);
v_diag_672_ = lean_ctor_get(v___x_668_, 4);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_668_, 1);
lean_dec(v_unused_683_);
v___x_674_ = v___x_668_;
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_diag_672_);
lean_inc(v_postponed_671_);
lean_inc(v_zetaDeltaFVarIds_670_);
lean_inc(v_mctx_669_);
lean_dec(v___x_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_648_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_mctx_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_zetaDeltaFVarIds_670_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_postponed_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_diag_672_);
v___x_678_ = v_reuseFailAlloc_681_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_st_ref_put(v___y_647_, v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_676_);
return v___x_680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0___boxed(lean_object* v___y_687_, lean_object* v_isExporting_688_, lean_object* v___x_689_, lean_object* v___y_690_, lean_object* v___x_691_, lean_object* v_a_x3f_692_, lean_object* v___y_693_){
_start:
{
uint8_t v_isExporting_boxed_694_; lean_object* v_res_695_; 
v_isExporting_boxed_694_ = lean_unbox(v_isExporting_688_);
v_res_695_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_687_, v_isExporting_boxed_694_, v___x_689_, v___y_690_, v___x_691_, v_a_x3f_692_);
lean_dec(v_a_x3f_692_);
lean_dec(v___y_690_);
lean_dec(v___y_687_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(lean_object* v_x_696_, uint8_t v_isExporting_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_env_704_; lean_object* v___x_705_; uint8_t v_isModule_706_; 
v___x_703_ = lean_st_ref_get(v___y_701_);
v_env_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc_ref(v_env_704_);
lean_dec(v___x_703_);
v___x_705_ = l_Lean_Environment_header(v_env_704_);
v_isModule_706_ = lean_ctor_get_uint8(v___x_705_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_705_);
if (v_isModule_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec_ref(v_env_704_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_707_ = lean_apply_5(v_x_696_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
return v___x_707_;
}
else
{
uint8_t v_isExporting_708_; 
v_isExporting_708_ = lean_ctor_get_uint8(v_env_704_, sizeof(void*)*13);
lean_dec_ref(v_env_704_);
if (v_isExporting_697_ == 0)
{
if (v_isExporting_708_ == 0)
{
lean_object* v___x_775_; 
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_775_ = lean_apply_5(v_x_696_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
return v___x_775_;
}
else
{
goto v___jp_709_;
}
}
else
{
if (v_isExporting_708_ == 0)
{
goto v___jp_709_;
}
else
{
lean_object* v___x_776_; 
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_776_ = lean_apply_5(v_x_696_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
return v___x_776_;
}
}
v___jp_709_:
{
lean_object* v___x_710_; lean_object* v_env_711_; lean_object* v_nextMacroScope_712_; lean_object* v_ngen_713_; lean_object* v_auxDeclNGen_714_; lean_object* v_traceState_715_; lean_object* v_recordedDeps_716_; lean_object* v_messages_717_; lean_object* v_infoState_718_; lean_object* v_snapshotTasks_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_773_; 
v___x_710_ = lean_st_ref_take(v___y_701_);
v_env_711_ = lean_ctor_get(v___x_710_, 0);
v_nextMacroScope_712_ = lean_ctor_get(v___x_710_, 1);
v_ngen_713_ = lean_ctor_get(v___x_710_, 2);
v_auxDeclNGen_714_ = lean_ctor_get(v___x_710_, 3);
v_traceState_715_ = lean_ctor_get(v___x_710_, 4);
v_recordedDeps_716_ = lean_ctor_get(v___x_710_, 6);
v_messages_717_ = lean_ctor_get(v___x_710_, 7);
v_infoState_718_ = lean_ctor_get(v___x_710_, 8);
v_snapshotTasks_719_ = lean_ctor_get(v___x_710_, 9);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v___x_710_, 5);
lean_dec(v_unused_774_);
v___x_721_ = v___x_710_;
v_isShared_722_ = v_isSharedCheck_773_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_snapshotTasks_719_);
lean_inc(v_infoState_718_);
lean_inc(v_messages_717_);
lean_inc(v_recordedDeps_716_);
lean_inc(v_traceState_715_);
lean_inc(v_auxDeclNGen_714_);
lean_inc(v_ngen_713_);
lean_inc(v_nextMacroScope_712_);
lean_inc(v_env_711_);
lean_dec(v___x_710_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_773_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_723_ = l_Lean_Environment_setExporting(v_env_711_, v_isExporting_697_);
v___x_724_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 5, v___x_724_);
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_nextMacroScope_712_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_ngen_713_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_auxDeclNGen_714_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_traceState_715_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_772_, 6, v_recordedDeps_716_);
lean_ctor_set(v_reuseFailAlloc_772_, 7, v_messages_717_);
lean_ctor_set(v_reuseFailAlloc_772_, 8, v_infoState_718_);
lean_ctor_set(v_reuseFailAlloc_772_, 9, v_snapshotTasks_719_);
v___x_726_ = v_reuseFailAlloc_772_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_mctx_729_; lean_object* v_zetaDeltaFVarIds_730_; lean_object* v_postponed_731_; lean_object* v_diag_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_770_; 
v___x_727_ = lean_st_ref_put(v___y_701_, v___x_726_);
v___x_728_ = lean_st_ref_take(v___y_699_);
v_mctx_729_ = lean_ctor_get(v___x_728_, 0);
v_zetaDeltaFVarIds_730_ = lean_ctor_get(v___x_728_, 2);
v_postponed_731_ = lean_ctor_get(v___x_728_, 3);
v_diag_732_ = lean_ctor_get(v___x_728_, 4);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v___x_728_, 1);
lean_dec(v_unused_771_);
v___x_734_ = v___x_728_;
v_isShared_735_ = v_isSharedCheck_770_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_diag_732_);
lean_inc(v_postponed_731_);
lean_inc(v_zetaDeltaFVarIds_730_);
lean_inc(v_mctx_729_);
lean_dec(v___x_728_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_770_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_mctx_729_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_zetaDeltaFVarIds_730_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_postponed_731_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_diag_732_);
v___x_738_ = v_reuseFailAlloc_769_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v_r_740_; 
v___x_739_ = lean_st_ref_put(v___y_699_, v___x_738_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v_r_740_ = lean_apply_5(v_x_696_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
if (lean_obj_tag(v_r_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_757_; 
v_a_741_ = lean_ctor_get(v_r_740_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_r_740_);
if (v_isSharedCheck_757_ == 0)
{
v___x_743_ = v_r_740_;
v_isShared_744_ = v_isSharedCheck_757_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v_r_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_757_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
lean_inc(v_a_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 1);
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_756_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v___x_747_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_701_, v_isExporting_708_, v___x_724_, v___y_699_, v___x_736_, v___x_746_);
lean_dec_ref(v___x_746_);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_747_, 0);
lean_dec(v_unused_755_);
v___x_749_ = v___x_747_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_dec(v___x_747_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v_a_741_);
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_741_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_758_ = lean_ctor_get(v_r_740_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v_r_740_, 1);
v___x_759_ = lean_box(0);
v___x_760_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___lam__0(v___y_701_, v_isExporting_708_, v___x_724_, v___y_699_, v___x_736_, v___x_759_);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v___x_760_, 0);
lean_dec(v_unused_768_);
v___x_762_ = v___x_760_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_dec(v___x_760_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 1);
lean_ctor_set(v___x_762_, 0, v_a_758_);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_758_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg___boxed(lean_object* v_x_777_, lean_object* v_isExporting_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
uint8_t v_isExporting_boxed_784_; lean_object* v_res_785_; 
v_isExporting_boxed_784_ = lean_unbox(v_isExporting_778_);
v_res_785_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_777_, v_isExporting_boxed_784_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object* v_declName_786_, uint8_t v_post_787_, uint8_t v_inv_788_, uint8_t v_attrKind_789_, lean_object* v_prio_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___y_802_; uint8_t v___x_825_; uint8_t v___x_826_; 
v___x_796_ = 1;
v___x_797_ = lean_box(v_post_787_);
v___x_798_ = lean_box(v_inv_788_);
v___x_799_ = lean_box(v___x_796_);
lean_inc(v_declName_786_);
v___x_800_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpTheoremFromConst___boxed), 10, 5);
lean_closure_set(v___x_800_, 0, v_declName_786_);
lean_closure_set(v___x_800_, 1, v___x_797_);
lean_closure_set(v___x_800_, 2, v___x_798_);
lean_closure_set(v___x_800_, 3, v_prio_790_);
lean_closure_set(v___x_800_, 4, v___x_799_);
v___x_825_ = 1;
v___x_826_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_789_, v___x_825_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_isPrivateName(v_declName_786_);
lean_dec(v_declName_786_);
if (v___x_827_ == 0)
{
v___y_802_ = v___x_796_;
goto v___jp_801_;
}
else
{
v___y_802_ = v___x_826_;
goto v___jp_801_;
}
}
else
{
uint8_t v___x_828_; 
lean_dec(v_declName_786_);
v___x_828_ = 0;
v___y_802_ = v___x_828_;
goto v___jp_801_;
}
v___jp_801_:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v___x_800_, v___y_802_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = lean_box(0);
v_sz_806_ = lean_array_size(v_a_804_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormTheorem_spec__2(v_attrKind_789_, v_post_787_, v_a_804_, v_sz_806_, v___x_807_, v___x_805_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_804_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_808_, 0);
lean_dec(v_unused_816_);
v___x_810_ = v___x_808_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_dec(v___x_808_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_805_);
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_805_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
return v___x_808_;
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
v_a_817_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_803_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_803_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormTheorem___boxed(lean_object* v_declName_829_, lean_object* v_post_830_, lean_object* v_inv_831_, lean_object* v_attrKind_832_, lean_object* v_prio_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
uint8_t v_post_boxed_839_; uint8_t v_inv_boxed_840_; uint8_t v_attrKind_boxed_841_; lean_object* v_res_842_; 
v_post_boxed_839_ = lean_unbox(v_post_830_);
v_inv_boxed_840_ = lean_unbox(v_inv_831_);
v_attrKind_boxed_841_ = lean_unbox(v_attrKind_832_);
v_res_842_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_829_, v_post_boxed_839_, v_inv_boxed_840_, v_attrKind_boxed_841_, v_prio_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(lean_object* v_00_u03b1_843_, lean_object* v_x_844_, uint8_t v_isExporting_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_844_, v_isExporting_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___boxed(lean_object* v_00_u03b1_852_, lean_object* v_x_853_, lean_object* v_isExporting_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_isExporting_boxed_860_; lean_object* v_res_861_; 
v_isExporting_boxed_860_ = lean_unbox(v_isExporting_854_);
v_res_861_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0(v_00_u03b1_852_, v_x_853_, v_isExporting_boxed_860_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_00_u03c3_864_, lean_object* v_ext_865_, lean_object* v_b_866_, uint8_t v_kind_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v_ext_865_, v_b_866_, v_kind_867_, v___y_869_, v___y_870_, v___y_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___boxed(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_00_u03c3_876_, lean_object* v_ext_877_, lean_object* v_b_878_, lean_object* v_kind_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v_kind_boxed_885_; lean_object* v_res_886_; 
v_kind_boxed_885_ = lean_unbox(v_kind_879_);
v_res_886_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1(v_00_u03b1_874_, v_00_u03b2_875_, v_00_u03c3_876_, v_ext_877_, v_b_878_, v_kind_boxed_885_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0___redArg();
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0_spec__0(lean_object* v_00_u03b2_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(uint8_t v_attrKind_895_, lean_object* v_as_896_, size_t v_sz_897_, size_t v_i_898_, lean_object* v_b_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_lt(v_i_898_, v_sz_897_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v_b_899_);
return v___x_905_;
}
else
{
lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_906_ = lean_box(0);
v_a_907_ = lean_array_uget_borrowed(v_as_896_, v_i_898_);
v___x_908_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_907_);
v___x_909_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_909_, 0, v_a_907_);
v___x_910_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_908_, v___x_909_, v_attrKind_895_, v___y_900_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_910_) == 0)
{
size_t v___x_911_; size_t v___x_912_; 
lean_dec_ref_known(v___x_910_, 1);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_898_, v___x_911_);
v_i_898_ = v___x_912_;
v_b_899_ = v___x_906_;
goto _start;
}
else
{
return v___x_910_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg___boxed(lean_object* v_attrKind_914_, lean_object* v_as_915_, lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v_attrKind_boxed_923_; size_t v_sz_boxed_924_; size_t v_i_boxed_925_; lean_object* v_res_926_; 
v_attrKind_boxed_923_ = lean_unbox(v_attrKind_914_);
v_sz_boxed_924_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_925_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_boxed_923_, v_as_915_, v_sz_boxed_924_, v_i_boxed_925_, v_b_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v_as_915_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(lean_object* v_declName_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_env_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_930_ = lean_st_ref_get(v___y_928_);
v_env_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_env_931_);
lean_dec(v___x_930_);
v___x_932_ = l_Lean_getReducibilityStatusCore(v_env_931_, v_declName_927_);
v___x_933_ = lean_box(v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg___boxed(lean_object* v_declName_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_935_, v___y_936_);
lean_dec(v___y_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(lean_object* v_declName_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_961_; 
v___x_945_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_939_, v___y_943_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_961_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_961_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_961_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___x_950_; 
v___x_950_ = lean_unbox(v_a_946_);
lean_dec(v_a_946_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_951_ = 1;
v___x_952_ = lean_box(v___x_951_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_952_);
v___x_954_ = v___x_948_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_956_ = 0;
v___x_957_ = lean_box(v___x_956_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_957_);
v___x_959_ = v___x_948_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0___boxed(lean_object* v_declName_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(uint8_t v_attrKind_969_, lean_object* v_as_970_, size_t v_sz_971_, size_t v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_lt(v_i_972_, v_sz_971_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v_b_973_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_980_ = lean_box(0);
v_a_981_ = lean_array_uget_borrowed(v_as_970_, v_i_972_);
v___x_982_ = l_Lean_Meta_Grind_normSymExt;
lean_inc(v_a_981_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_a_981_);
v___x_984_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg(v___x_982_, v___x_983_, v_attrKind_969_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_984_) == 0)
{
size_t v___x_985_; size_t v___x_986_; 
lean_dec_ref_known(v___x_984_, 1);
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_add(v_i_972_, v___x_985_);
v_i_972_ = v___x_986_;
v_b_973_ = v___x_980_;
goto _start;
}
else
{
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg___boxed(lean_object* v_attrKind_988_, lean_object* v_as_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_b_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v_attrKind_boxed_997_; size_t v_sz_boxed_998_; size_t v_i_boxed_999_; lean_object* v_res_1000_; 
v_attrKind_boxed_997_ = lean_unbox(v_attrKind_988_);
v_sz_boxed_998_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_999_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_boxed_997_, v_as_989_, v_sz_boxed_998_, v_i_boxed_999_, v_b_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v_as_989_);
return v_res_1000_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__0));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object* v_declName_1004_, uint8_t v_attrKind_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1014_; 
lean_inc(v_declName_1004_);
v___x_1014_ = l_Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0(v_declName_1004_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1081_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1081_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1081_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___y_1020_; lean_object* v_a_1021_; uint8_t v___x_1040_; 
v___x_1040_ = lean_unbox(v_a_1015_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_del_object(v___x_1017_);
lean_inc(v_declName_1004_);
v___x_1041_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_declName_1004_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; size_t v_sz_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = lean_box(0);
v_sz_1044_ = lean_array_size(v_a_1042_);
v___x_1045_ = ((size_t)0ULL);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1005_, v_a_1042_, v_sz_1044_, v___x_1045_, v___x_1043_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1042_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref_known(v___x_1046_, 1);
lean_inc(v_declName_1004_);
v___x_1047_ = l_Lean_Meta_Sym_DSimp_Decls_mkEntries(v_declName_1004_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; size_t v_sz_1049_; lean_object* v___x_1050_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v_sz_1049_ = lean_array_size(v_a_1048_);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1005_, v_a_1048_, v_sz_1049_, v___x_1045_, v___x_1043_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1048_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1015_);
lean_dec(v_declName_1004_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1058_);
v___x_1052_ = v___x_1050_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1043_);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1043_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1059_; 
v_a_1059_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1059_);
v___y_1020_ = v___x_1050_;
v_a_1021_ = v_a_1059_;
goto v___jp_1019_;
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1047_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1047_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
lean_inc(v_a_1060_);
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
v___y_1020_ = v___x_1065_;
v_a_1021_ = v_a_1060_;
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v_a_1068_; 
v_a_1068_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1068_);
v___y_1020_ = v___x_1046_;
v_a_1021_ = v_a_1068_;
goto v___jp_1019_;
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1041_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1041_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
lean_inc(v_a_1069_);
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
v___y_1020_ = v___x_1074_;
v_a_1021_ = v_a_1069_;
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec(v_a_1015_);
lean_dec(v_declName_1004_);
v___x_1077_ = lean_box(0);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1077_);
v___x_1079_ = v___x_1017_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
v___jp_1019_:
{
uint8_t v___x_1022_; 
v___x_1022_ = l_Lean_Exception_isInterrupt(v_a_1021_);
if (v___x_1022_ == 0)
{
uint8_t v___x_1023_; 
lean_inc_ref(v_a_1021_);
v___x_1023_ = l_Lean_Exception_isRuntime(v_a_1021_);
if (v___x_1023_ == 0)
{
lean_object* v_toCold_1024_; lean_object* v_options_1025_; uint8_t v_hasTrace_1026_; 
lean_dec_ref(v___y_1020_);
v_toCold_1024_ = lean_ctor_get(v_a_1008_, 0);
v_options_1025_ = lean_ctor_get(v_toCold_1024_, 2);
v_hasTrace_1026_ = lean_ctor_get_uint8(v_options_1025_, sizeof(void*)*1);
if (v_hasTrace_1026_ == 0)
{
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1015_);
lean_dec(v_declName_1004_);
goto v___jp_1011_;
}
else
{
lean_object* v_inheritedTraceOptions_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_inheritedTraceOptions_1027_ = lean_ctor_get(v_toCold_1024_, 11);
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_448808965____hygCtx___hyg_2_));
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__2);
v___x_1030_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1027_, v_options_1025_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1015_);
lean_dec(v_declName_1004_);
goto v___jp_1011_;
}
else
{
lean_object* v___x_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1031_ = lean_obj_once(&l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1, &l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1_once, _init_l_Lean_Meta_Grind_addNormSymDeclToUnfold___closed__1);
v___x_1032_ = lean_unbox(v_a_1015_);
lean_dec(v_a_1015_);
v___x_1033_ = l_Lean_MessageData_ofConstName(v_declName_1004_, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1031_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__6);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_Exception_toMessageData(v_a_1021_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v___x_1028_, v___x_1038_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1039_;
}
}
}
else
{
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1015_);
lean_dec(v_declName_1004_);
return v___y_1020_;
}
}
else
{
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1015_);
lean_dec(v_declName_1004_);
return v___y_1020_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_declName_1004_);
v_a_1082_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1014_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1014_);
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
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold___boxed(lean_object* v_declName_1090_, lean_object* v_attrKind_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
uint8_t v_attrKind_boxed_1097_; lean_object* v_res_1098_; 
v_attrKind_boxed_1097_ = lean_unbox(v_attrKind_1091_);
v_res_1098_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1090_, v_attrKind_boxed_1097_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(lean_object* v_declName_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___redArg(v_declName_1099_, v___y_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0___boxed(lean_object* v_declName_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__0_spec__0(v_declName_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(uint8_t v_attrKind_1113_, lean_object* v_as_1114_, size_t v_sz_1115_, size_t v_i_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___redArg(v_attrKind_1113_, v_as_1114_, v_sz_1115_, v_i_1116_, v_b_1117_, v___y_1119_, v___y_1120_, v___y_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1___boxed(lean_object* v_attrKind_1124_, lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v_attrKind_boxed_1134_; size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_attrKind_boxed_1134_ = lean_unbox(v_attrKind_1124_);
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__1(v_attrKind_boxed_1134_, v_as_1125_, v_sz_boxed_1135_, v_i_boxed_1136_, v_b_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_as_1125_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(uint8_t v_attrKind_1138_, lean_object* v_as_1139_, size_t v_sz_1140_, size_t v_i_1141_, lean_object* v_b_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___redArg(v_attrKind_1138_, v_as_1139_, v_sz_1140_, v_i_1141_, v_b_1142_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2___boxed(lean_object* v_attrKind_1149_, lean_object* v_as_1150_, lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v_attrKind_boxed_1159_; size_t v_sz_boxed_1160_; size_t v_i_boxed_1161_; lean_object* v_res_1162_; 
v_attrKind_boxed_1159_ = lean_unbox(v_attrKind_1149_);
v_sz_boxed_1160_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1161_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_addNormSymDeclToUnfold_spec__2(v_attrKind_boxed_1159_, v_as_1150_, v_sz_boxed_1160_, v_i_boxed_1161_, v_b_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_as_1150_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold(lean_object* v_declName_1163_, uint8_t v_attrKind_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1170_ = l_Lean_Meta_Grind_normExt;
v___x_1171_ = 0;
v___x_1172_ = lean_unsigned_to_nat(1000u);
lean_inc(v_declName_1163_);
v___x_1173_ = l_Lean_Meta_addDeclToUnfold(v___x_1170_, v_declName_1163_, v___x_1171_, v___x_1171_, v___x_1172_, v_attrKind_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1200_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1200_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1200_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_unbox(v_a_1174_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
lean_dec(v_a_1174_);
lean_dec(v_declName_1163_);
v___x_1179_ = lean_box(v___x_1171_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1179_);
v___x_1181_ = v___x_1176_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
else
{
lean_object* v___x_1183_; 
lean_del_object(v___x_1176_);
v___x_1183_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v_declName_1163_, v_attrKind_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v___x_1183_, 0);
lean_dec(v_unused_1191_);
v___x_1185_ = v___x_1183_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v___x_1183_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_a_1174_);
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1174_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_a_1174_);
v_a_1192_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1183_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1183_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_1163_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNormDeclToUnfold___boxed(lean_object* v_declName_1201_, lean_object* v_attrKind_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
uint8_t v_attrKind_boxed_1208_; lean_object* v_res_1209_; 
v_attrKind_boxed_1208_ = lean_unbox(v_attrKind_1202_);
v_res_1209_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_1201_, v_attrKind_boxed_1208_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(lean_object* v_x_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_tag_nat(v_x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___impl___boxed(lean_object* v_x_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_Grind_AttrKind_ctorIdx___impl(v_x_1212_);
lean_dec(v_x_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_1214_, lean_object* v_k_1215_){
_start:
{
switch(lean_obj_tag(v_t_1214_))
{
case 0:
{
lean_object* v_k_1216_; lean_object* v___x_1217_; 
v_k_1216_ = lean_ctor_get(v_t_1214_, 0);
lean_inc(v_k_1216_);
lean_dec_ref_known(v_t_1214_, 1);
v___x_1217_ = lean_apply_1(v_k_1215_, v_k_1216_);
return v___x_1217_;
}
case 1:
{
uint8_t v_eager_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_eager_1218_ = lean_ctor_get_uint8(v_t_1214_, 0);
lean_dec_ref_known(v_t_1214_, 0);
v___x_1219_ = lean_box(v_eager_1218_);
v___x_1220_ = lean_apply_1(v_k_1215_, v___x_1219_);
return v___x_1220_;
}
case 5:
{
lean_object* v_prio_1221_; lean_object* v___x_1222_; 
v_prio_1221_ = lean_ctor_get(v_t_1214_, 0);
lean_inc(v_prio_1221_);
lean_dec_ref_known(v_t_1214_, 1);
v___x_1222_ = lean_apply_1(v_k_1215_, v_prio_1221_);
return v___x_1222_;
}
case 8:
{
uint8_t v_post_1223_; uint8_t v_inv_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_post_1223_ = lean_ctor_get_uint8(v_t_1214_, 0);
v_inv_1224_ = lean_ctor_get_uint8(v_t_1214_, 1);
lean_dec_ref_known(v_t_1214_, 0);
v___x_1225_ = lean_box(v_post_1223_);
v___x_1226_ = lean_box(v_inv_1224_);
v___x_1227_ = lean_apply_2(v_k_1215_, v___x_1225_, v___x_1226_);
return v___x_1227_;
}
case 10:
{
uint8_t v_fallback_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_fallback_1228_ = lean_ctor_get_uint8(v_t_1214_, 0);
lean_dec_ref_known(v_t_1214_, 0);
v___x_1229_ = lean_box(v_fallback_1228_);
v___x_1230_ = lean_apply_1(v_k_1215_, v___x_1229_);
return v___x_1230_;
}
default: 
{
lean_dec(v_t_1214_);
return v_k_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_1231_, lean_object* v_ctorIdx_1232_, lean_object* v_t_1233_, lean_object* v_h_1234_, lean_object* v_k_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1233_, v_k_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_1237_, lean_object* v_ctorIdx_1238_, lean_object* v_t_1239_, lean_object* v_h_1240_, lean_object* v_k_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_1237_, v_ctorIdx_1238_, v_t_1239_, v_h_1240_, v_k_1241_);
lean_dec(v_ctorIdx_1238_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_1243_, lean_object* v_ematch_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1243_, v_ematch_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_1246_, lean_object* v_t_1247_, lean_object* v_h_1248_, lean_object* v_ematch_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1247_, v_ematch_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_1251_, lean_object* v_cases_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1251_, v_cases_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_1254_, lean_object* v_t_1255_, lean_object* v_h_1256_, lean_object* v_cases_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1255_, v_cases_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_1259_, lean_object* v_intro_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1259_, v_intro_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_1262_, lean_object* v_t_1263_, lean_object* v_h_1264_, lean_object* v_intro_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1263_, v_intro_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_1267_, lean_object* v_infer_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1267_, v_infer_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_1270_, lean_object* v_t_1271_, lean_object* v_h_1272_, lean_object* v_infer_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1271_, v_infer_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_1275_, lean_object* v_ext_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1275_, v_ext_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_1278_, lean_object* v_t_1279_, lean_object* v_h_1280_, lean_object* v_ext_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1279_, v_ext_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_1283_, lean_object* v_symbol_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1283_, v_symbol_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_1286_, lean_object* v_t_1287_, lean_object* v_h_1288_, lean_object* v_symbol_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1287_, v_symbol_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_1291_, lean_object* v_inj_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1291_, v_inj_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_1294_, lean_object* v_t_1295_, lean_object* v_h_1296_, lean_object* v_inj_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1295_, v_inj_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_1299_, lean_object* v_funCC_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1299_, v_funCC_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_1302_, lean_object* v_t_1303_, lean_object* v_h_1304_, lean_object* v_funCC_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1303_, v_funCC_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_1307_, lean_object* v_norm_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1307_, v_norm_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_1310_, lean_object* v_t_1311_, lean_object* v_h_1312_, lean_object* v_norm_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1311_, v_norm_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_1315_, lean_object* v_unfold_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1315_, v_unfold_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_1318_, lean_object* v_t_1319_, lean_object* v_h_1320_, lean_object* v_unfold_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1319_, v_unfold_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_1323_, lean_object* v_homo_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1323_, v_homo_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_1326_, lean_object* v_t_1327_, lean_object* v_h_1328_, lean_object* v_homo_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1327_, v_homo_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_1331_, lean_object* v_homoPred_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1331_, v_homoPred_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_1334_, lean_object* v_t_1335_, lean_object* v_h_1336_, lean_object* v_homoPred_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_1335_, v_homoPred_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1341_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
lean_ctor_set(v___x_1344_, 3, v___x_1343_);
lean_ctor_set(v___x_1344_, 4, v___x_1342_);
lean_ctor_set(v___x_1344_, 5, v___x_1342_);
lean_ctor_set(v___x_1344_, 6, v___x_1342_);
lean_ctor_set(v___x_1344_, 7, v___x_1342_);
lean_ctor_set(v___x_1344_, 8, v___x_1342_);
lean_ctor_set(v___x_1344_, 9, v___x_1342_);
lean_ctor_set(v___x_1344_, 10, v___x_1342_);
lean_ctor_set(v___x_1344_, 11, v___x_1341_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_unsigned_to_nat(32u);
v___x_1346_ = lean_mk_empty_array_with_capacity(v___x_1345_);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1348_ = ((size_t)5ULL);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_unsigned_to_nat(32u);
v___x_1351_ = lean_mk_empty_array_with_capacity(v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_1353_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
lean_ctor_set(v___x_1353_, 2, v___x_1349_);
lean_ctor_set(v___x_1353_, 3, v___x_1349_);
lean_ctor_set_usize(v___x_1353_, 4, v___x_1348_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = lean_box(1);
v___x_1355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_1356_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___x_1355_);
lean_ctor_set(v___x_1357_, 2, v___x_1354_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; lean_object* v_toCold_1363_; lean_object* v_env_1364_; lean_object* v_options_1365_; uint8_t v___x_1366_; lean_object* v_env_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1362_ = lean_st_ref_get(v___y_1360_);
v_toCold_1363_ = lean_ctor_get(v___y_1359_, 0);
v_env_1364_ = lean_ctor_get(v___x_1362_, 0);
lean_inc_ref(v_env_1364_);
lean_dec(v___x_1362_);
v_options_1365_ = lean_ctor_get(v_toCold_1363_, 2);
v___x_1366_ = 0;
v_env_1367_ = l_Lean_Environment_setRecordingDeps(v_env_1364_, v___x_1366_);
v___x_1368_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_1369_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_1365_);
v___x_1370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1370_, 0, v_env_1367_);
lean_ctor_set(v___x_1370_, 1, v___x_1368_);
lean_ctor_set(v___x_1370_, 2, v___x_1369_);
lean_ctor_set(v___x_1370_, 3, v_options_1365_);
v___x_1371_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v_msgData_1358_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_ref_1382_; lean_object* v___x_1383_; lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1392_; 
v_ref_1382_ = lean_ctor_get(v___y_1379_, 2);
v___x_1383_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_1378_, v___y_1379_, v___y_1380_);
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_inc(v_ref_1382_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_ref_1382_);
lean_ctor_set(v___x_1388_, 1, v_a_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 1);
lean_ctor_set(v___x_1386_, 0, v___x_1388_);
v___x_1390_ = v___x_1386_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_1398_, lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_toCold_1403_; lean_object* v_currRecDepth_1404_; lean_object* v_ref_1405_; uint16_t v_optionFlags_1406_; uint8_t v_suppressElabErrors_1407_; uint8_t v_checkDeprecated_1408_; uint8_t v_isRecordingDeps_1409_; lean_object* v_ref_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_toCold_1403_ = lean_ctor_get(v___y_1400_, 0);
v_currRecDepth_1404_ = lean_ctor_get(v___y_1400_, 1);
v_ref_1405_ = lean_ctor_get(v___y_1400_, 2);
v_optionFlags_1406_ = lean_ctor_get_uint16(v___y_1400_, sizeof(void*)*3);
v_suppressElabErrors_1407_ = lean_ctor_get_uint8(v___y_1400_, sizeof(void*)*3 + 2);
v_checkDeprecated_1408_ = lean_ctor_get_uint8(v___y_1400_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1409_ = lean_ctor_get_uint8(v___y_1400_, sizeof(void*)*3 + 4);
v_ref_1410_ = l_Lean_replaceRef(v_ref_1398_, v_ref_1405_);
lean_inc(v_currRecDepth_1404_);
lean_inc_ref(v_toCold_1403_);
v___x_1411_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1411_, 0, v_toCold_1403_);
lean_ctor_set(v___x_1411_, 1, v_currRecDepth_1404_);
lean_ctor_set(v___x_1411_, 2, v_ref_1410_);
lean_ctor_set_uint16(v___x_1411_, sizeof(void*)*3, v_optionFlags_1406_);
lean_ctor_set_uint8(v___x_1411_, sizeof(void*)*3 + 2, v_suppressElabErrors_1407_);
lean_ctor_set_uint8(v___x_1411_, sizeof(void*)*3 + 3, v_checkDeprecated_1408_);
lean_ctor_set_uint8(v___x_1411_, sizeof(void*)*3 + 4, v_isRecordingDeps_1409_);
v___x_1412_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1399_, v___x_1411_, v___y_1401_);
lean_dec_ref_known(v___x_1411_, 3);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_1413_, lean_object* v_msg_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1413_, v_msg_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v_ref_1413_);
return v_res_1418_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
v___x_1428_ = l_Lean_stringToMessageData(v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__5));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__2));
lean_inc(v_stx_1599_);
v___x_1604_ = l_Lean_Syntax_isOfKind(v_stx_1599_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1606_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1609_, v_a_1600_, v_a_1601_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = l_Lean_Syntax_getArg(v_stx_1599_, v___x_1611_);
v___x_1613_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__8));
lean_inc(v___x_1612_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__10));
lean_inc(v___x_1612_);
v___x_1616_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__12));
lean_inc(v___x_1612_);
v___x_1618_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__14));
lean_inc(v___x_1612_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__16));
lean_inc(v___x_1612_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__18));
lean_inc(v___x_1612_);
v___x_1624_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__20));
lean_inc(v___x_1612_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__22));
lean_inc(v___x_1612_);
v___x_1628_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__24));
lean_inc(v___x_1612_);
v___x_1630_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__26));
lean_inc(v___x_1612_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
lean_inc(v___x_1612_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__30));
lean_inc(v___x_1612_);
v___x_1636_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__32));
lean_inc(v___x_1612_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__34));
lean_inc(v___x_1612_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__36));
lean_inc(v___x_1612_);
v___x_1642_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__38));
lean_inc(v___x_1612_);
v___x_1644_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__40));
lean_inc(v___x_1612_);
v___x_1646_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__42));
lean_inc(v___x_1612_);
v___x_1648_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__44));
lean_inc(v___x_1612_);
v___x_1650_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__46));
lean_inc(v___x_1612_);
v___x_1652_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__48));
lean_inc(v___x_1612_);
v___x_1654_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__50));
lean_inc(v___x_1612_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
lean_inc(v___x_1612_);
v___x_1658_ = l_Lean_Syntax_isOfKind(v___x_1612_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v___x_1612_);
v___x_1659_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1660_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1663_, v_a_1600_, v_a_1601_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_stx_1599_);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1665_);
lean_dec(v___x_1612_);
v___x_1667_ = l_Lean_Syntax_isNatLit_x3f(v___x_1666_);
if (lean_obj_tag(v___x_1667_) == 1)
{
lean_object* v_val_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v___x_1666_);
v_val_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_val_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 5);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_val_1668_);
v___x_1673_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___x_1667_);
v___x_1677_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__54, &l_Lean_Meta_Grind_getAttrKindCore___closed__54_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__54);
v___x_1678_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_1666_, v___x_1677_, v_a_1600_, v_a_1601_);
lean_dec(v___x_1666_);
return v___x_1678_;
}
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1679_ = lean_box(11);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1681_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1681_, 0, v___x_1604_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1683_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_1683_, 0, v___x_1650_);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1685_ = lean_box(9);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1687_);
lean_inc(v___x_1688_);
v___x_1689_ = l_Lean_Syntax_matchesNull(v___x_1688_, v___x_1611_);
if (v___x_1689_ == 0)
{
uint8_t v___x_1690_; 
lean_inc(v___x_1688_);
v___x_1690_ = l_Lean_Syntax_matchesNull(v___x_1688_, v___x_1687_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v___x_1688_);
lean_dec(v___x_1612_);
v___x_1691_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1692_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1695_, v_a_1600_, v_a_1601_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1697_ = l_Lean_Syntax_getArg(v___x_1688_, v___x_1611_);
lean_dec(v___x_1688_);
v___x_1698_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_1697_);
v___x_1699_ = l_Lean_Syntax_isOfKind(v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_1701_ = l_Lean_Syntax_isOfKind(v___x_1697_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v___x_1612_);
v___x_1702_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1703_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1706_, v_a_1600_, v_a_1601_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1708_ = lean_unsigned_to_nat(2u);
v___x_1709_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1708_);
lean_dec(v___x_1612_);
lean_inc(v___x_1709_);
v___x_1710_ = l_Lean_Syntax_matchesNull(v___x_1709_, v___x_1611_);
if (v___x_1710_ == 0)
{
uint8_t v___x_1711_; 
v___x_1711_ = l_Lean_Syntax_matchesNull(v___x_1709_, v___x_1687_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1712_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1713_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1716_, v_a_1600_, v_a_1601_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v_stx_1599_);
v___x_1718_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1718_, 0, v___x_1710_);
lean_ctor_set_uint8(v___x_1718_, 1, v___x_1604_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec(v___x_1709_);
lean_dec(v_stx_1599_);
v___x_1720_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1720_, 0, v___x_1699_);
lean_ctor_set_uint8(v___x_1720_, 1, v___x_1699_);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
lean_dec(v___x_1697_);
v___x_1722_ = lean_unsigned_to_nat(2u);
v___x_1723_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1722_);
lean_dec(v___x_1612_);
lean_inc(v___x_1723_);
v___x_1724_ = l_Lean_Syntax_matchesNull(v___x_1723_, v___x_1611_);
if (v___x_1724_ == 0)
{
uint8_t v___x_1725_; 
v___x_1725_ = l_Lean_Syntax_matchesNull(v___x_1723_, v___x_1687_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1726_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1727_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1730_, v_a_1600_, v_a_1601_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_stx_1599_);
v___x_1732_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1732_, 0, v___x_1604_);
lean_ctor_set_uint8(v___x_1732_, 1, v___x_1604_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v___x_1723_);
lean_dec(v_stx_1599_);
v___x_1734_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1734_, 0, v___x_1604_);
lean_ctor_set_uint8(v___x_1734_, 1, v___x_1689_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
lean_dec(v___x_1688_);
v___x_1736_ = lean_unsigned_to_nat(2u);
v___x_1737_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1736_);
lean_dec(v___x_1612_);
lean_inc(v___x_1737_);
v___x_1738_ = l_Lean_Syntax_matchesNull(v___x_1737_, v___x_1611_);
if (v___x_1738_ == 0)
{
uint8_t v___x_1739_; 
v___x_1739_ = l_Lean_Syntax_matchesNull(v___x_1737_, v___x_1687_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1740_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1741_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1744_, v_a_1600_, v_a_1601_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v_stx_1599_);
v___x_1746_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1746_, 0, v___x_1604_);
lean_ctor_set_uint8(v___x_1746_, 1, v___x_1604_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v___x_1737_);
lean_dec(v_stx_1599_);
v___x_1748_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_1748_, 0, v___x_1604_);
lean_ctor_set_uint8(v___x_1748_, 1, v___x_1646_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1750_ = lean_box(7);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1752_ = lean_box(6);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1754_ = lean_box(4);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1756_ = lean_box(2);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1758_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1758_, 0, v___x_1604_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1760_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1760_, 0, v___x_1634_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1762_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1762_, 0, v___x_1604_);
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
return v___x_1764_;
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1765_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1767_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1771_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = lean_unsigned_to_nat(3u);
v___x_1774_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1773_);
lean_dec(v___x_1612_);
lean_inc(v___x_1774_);
v___x_1775_ = l_Lean_Syntax_matchesNull(v___x_1774_, v___x_1611_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1774_);
v___x_1777_ = l_Lean_Syntax_matchesNull(v___x_1774_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v___x_1774_);
v___x_1778_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1779_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1782_, v_a_1600_, v_a_1601_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = l_Lean_Syntax_getArg(v___x_1774_, v___x_1611_);
lean_dec(v___x_1774_);
v___x_1785_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1786_ = l_Lean_Syntax_isOfKind(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1787_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1788_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1791_, v_a_1600_, v_a_1601_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec(v_stx_1599_);
v___x_1793_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1793_, 0, v___x_1604_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec(v___x_1774_);
lean_dec(v_stx_1599_);
v___x_1796_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1796_, 0, v___x_1622_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1799_ = lean_unsigned_to_nat(2u);
v___x_1800_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1799_);
lean_dec(v___x_1612_);
lean_inc(v___x_1800_);
v___x_1801_ = l_Lean_Syntax_matchesNull(v___x_1800_, v___x_1611_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1800_);
v___x_1803_ = l_Lean_Syntax_matchesNull(v___x_1800_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1800_);
v___x_1804_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1805_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1808_, v_a_1600_, v_a_1601_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = l_Lean_Syntax_getArg(v___x_1800_, v___x_1611_);
lean_dec(v___x_1800_);
v___x_1811_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1812_ = l_Lean_Syntax_isOfKind(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1813_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1814_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1817_, v_a_1600_, v_a_1601_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec(v_stx_1599_);
v___x_1819_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1819_, 0, v___x_1604_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v___x_1800_);
lean_dec(v_stx_1599_);
v___x_1822_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1822_, 0, v___x_1620_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1825_);
lean_dec(v___x_1612_);
lean_inc(v___x_1826_);
v___x_1827_ = l_Lean_Syntax_matchesNull(v___x_1826_, v___x_1611_);
if (v___x_1827_ == 0)
{
uint8_t v___x_1828_; 
lean_inc(v___x_1826_);
v___x_1828_ = l_Lean_Syntax_matchesNull(v___x_1826_, v___x_1825_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v___x_1826_);
v___x_1829_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1830_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1833_, v_a_1600_, v_a_1601_);
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = l_Lean_Syntax_getArg(v___x_1826_, v___x_1611_);
lean_dec(v___x_1826_);
v___x_1836_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1837_ = l_Lean_Syntax_isOfKind(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1838_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1839_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1842_, v_a_1600_, v_a_1601_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_stx_1599_);
v___x_1844_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1844_, 0, v___x_1604_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v___x_1826_);
lean_dec(v_stx_1599_);
v___x_1847_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_1847_, 0, v___x_1618_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v___x_1612_);
lean_dec(v_stx_1599_);
v___x_1850_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1852_);
lean_dec(v___x_1612_);
lean_inc(v___x_1853_);
v___x_1854_ = l_Lean_Syntax_matchesNull(v___x_1853_, v___x_1611_);
if (v___x_1854_ == 0)
{
uint8_t v___x_1855_; 
lean_inc(v___x_1853_);
v___x_1855_ = l_Lean_Syntax_matchesNull(v___x_1853_, v___x_1852_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec(v___x_1853_);
v___x_1856_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1857_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1860_, v_a_1600_, v_a_1601_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1862_ = l_Lean_Syntax_getArg(v___x_1853_, v___x_1611_);
lean_dec(v___x_1853_);
v___x_1863_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1864_ = l_Lean_Syntax_isOfKind(v___x_1862_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1865_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1866_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1869_, v_a_1600_, v_a_1601_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec(v_stx_1599_);
v___x_1871_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1871_, 0, v___x_1604_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec(v___x_1853_);
lean_dec(v_stx_1599_);
v___x_1874_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_1874_, 0, v___x_1614_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = l_Lean_Syntax_getArg(v___x_1612_, v___x_1877_);
lean_dec(v___x_1612_);
lean_inc(v___x_1878_);
v___x_1879_ = l_Lean_Syntax_matchesNull(v___x_1878_, v___x_1611_);
if (v___x_1879_ == 0)
{
uint8_t v___x_1880_; 
lean_inc(v___x_1878_);
v___x_1880_ = l_Lean_Syntax_matchesNull(v___x_1878_, v___x_1877_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v___x_1878_);
v___x_1881_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1882_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1885_, v_a_1600_, v_a_1601_);
return v___x_1886_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1887_ = l_Lean_Syntax_getArg(v___x_1878_, v___x_1611_);
lean_dec(v___x_1878_);
v___x_1888_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__28));
v___x_1889_ = l_Lean_Syntax_isOfKind(v___x_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1890_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__4, &l_Lean_Meta_Grind_getAttrKindCore___closed__4_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__4);
v___x_1891_ = l_Lean_MessageData_ofSyntax(v_stx_1599_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__6, &l_Lean_Meta_Grind_getAttrKindCore___closed__6_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__6);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1894_, v_a_1600_, v_a_1601_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_stx_1599_);
v___x_1896_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1896_, 0, v___x_1604_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
}
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec(v___x_1878_);
lean_dec(v_stx_1599_);
v___x_1899_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_1906_, lean_object* v_msg_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_1907_, v___y_1908_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_1912_, v_msg_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_1918_, lean_object* v_ref_1919_, lean_object* v_msg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_1919_, v_msg_1920_, v___y_1921_, v___y_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_ref_1926_, lean_object* v_msg_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_1925_, v_ref_1926_, v_msg_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v_ref_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = l_Lean_Syntax_getArg(v_stx_1932_, v___x_1936_);
v___x_1938_ = l_Lean_Syntax_isNone(v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = l_Lean_Syntax_getArg(v___x_1937_, v___x_1939_);
lean_dec(v___x_1937_);
v___x_1941_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_1940_, v_a_1933_, v_a_1934_);
return v___x_1941_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec(v___x_1937_);
v___x_1942_ = lean_box(3);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_stx_1944_);
return v_res_1948_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_1951_ = l_Lean_stringToMessageData(v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_1956_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_1955_, v_a_1952_, v_a_1953_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_1962_, v_a_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_1966_, v_a_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_1971_, lean_object* v_b_1972_, uint8_t v_kind_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_toCold_1977_; lean_object* v_currNamespace_1978_; lean_object* v___x_1979_; lean_object* v_env_1980_; lean_object* v_nextMacroScope_1981_; lean_object* v_ngen_1982_; lean_object* v_auxDeclNGen_1983_; lean_object* v_traceState_1984_; lean_object* v_recordedDeps_1985_; lean_object* v_messages_1986_; lean_object* v_infoState_1987_; lean_object* v_snapshotTasks_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2000_; 
v_toCold_1977_ = lean_ctor_get(v___y_1974_, 0);
v_currNamespace_1978_ = lean_ctor_get(v_toCold_1977_, 4);
v___x_1979_ = lean_st_ref_take(v___y_1975_);
v_env_1980_ = lean_ctor_get(v___x_1979_, 0);
v_nextMacroScope_1981_ = lean_ctor_get(v___x_1979_, 1);
v_ngen_1982_ = lean_ctor_get(v___x_1979_, 2);
v_auxDeclNGen_1983_ = lean_ctor_get(v___x_1979_, 3);
v_traceState_1984_ = lean_ctor_get(v___x_1979_, 4);
v_recordedDeps_1985_ = lean_ctor_get(v___x_1979_, 6);
v_messages_1986_ = lean_ctor_get(v___x_1979_, 7);
v_infoState_1987_ = lean_ctor_get(v___x_1979_, 8);
v_snapshotTasks_1988_ = lean_ctor_get(v___x_1979_, 9);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v___x_1979_, 5);
lean_dec(v_unused_2001_);
v___x_1990_ = v___x_1979_;
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_snapshotTasks_1988_);
lean_inc(v_infoState_1987_);
lean_inc(v_messages_1986_);
lean_inc(v_recordedDeps_1985_);
lean_inc(v_traceState_1984_);
lean_inc(v_auxDeclNGen_1983_);
lean_inc(v_ngen_1982_);
lean_inc(v_nextMacroScope_1981_);
lean_inc(v_env_1980_);
lean_dec(v___x_1979_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2000_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1992_ = lean_box(0);
lean_inc(v_currNamespace_1978_);
v___x_1993_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1980_, v_ext_1971_, v_b_1972_, v_kind_1973_, v_currNamespace_1978_);
v___x_1994_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 5, v___x_1994_);
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1996_ = v___x_1990_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_nextMacroScope_1981_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_ngen_1982_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_auxDeclNGen_1983_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_traceState_1984_);
lean_ctor_set(v_reuseFailAlloc_1999_, 5, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1999_, 6, v_recordedDeps_1985_);
lean_ctor_set(v_reuseFailAlloc_1999_, 7, v_messages_1986_);
lean_ctor_set(v_reuseFailAlloc_1999_, 8, v_infoState_1987_);
lean_ctor_set(v_reuseFailAlloc_1999_, 9, v_snapshotTasks_1988_);
v___x_1996_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_st_ref_put(v___y_1975_, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1992_);
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_2002_, lean_object* v_b_2003_, lean_object* v_kind_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v_kind_boxed_2008_; lean_object* v_res_2009_; 
v_kind_boxed_2008_ = lean_unbox(v_kind_2004_);
v_res_2009_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2002_, v_b_2003_, v_kind_boxed_2008_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_00_u03c3_2012_, lean_object* v_ext_2013_, lean_object* v_b_2014_, uint8_t v_kind_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2013_, v_b_2014_, v_kind_2015_, v___y_2016_, v___y_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_00_u03b2_2021_, lean_object* v_00_u03c3_2022_, lean_object* v_ext_2023_, lean_object* v_b_2024_, lean_object* v_kind_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v_kind_boxed_2029_; lean_object* v_res_2030_; 
v_kind_boxed_2029_ = lean_unbox(v_kind_2025_);
v_res_2030_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_2020_, v_00_u03b2_2021_, v_00_u03c3_2022_, v_ext_2023_, v_b_2024_, v_kind_boxed_2029_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_2031_, lean_object* v_declName_2032_, uint8_t v_eager_2033_, uint8_t v_attrKind_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; 
lean_inc(v_declName_2032_);
v___x_2038_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_2032_, v_eager_2033_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref_known(v___x_2038_, 1);
v___x_2039_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_2039_, 0, v_declName_2032_);
lean_ctor_set_uint8(v___x_2039_, sizeof(void*)*1, v_eager_2033_);
v___x_2040_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2031_, v___x_2039_, v_attrKind_2034_, v_a_2035_, v_a_2036_);
return v___x_2040_;
}
else
{
lean_dec(v_declName_2032_);
lean_dec_ref(v_ext_2031_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_2041_, lean_object* v_declName_2042_, lean_object* v_eager_2043_, lean_object* v_attrKind_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
uint8_t v_eager_boxed_2048_; uint8_t v_attrKind_boxed_2049_; lean_object* v_res_2050_; 
v_eager_boxed_2048_ = lean_unbox(v_eager_2043_);
v_attrKind_boxed_2049_ = lean_unbox(v_attrKind_2044_);
v_res_2050_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2041_, v_declName_2042_, v_eager_boxed_2048_, v_attrKind_boxed_2049_, v_a_2045_, v_a_2046_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_2051_, lean_object* v_declName_2052_, uint8_t v_attrKind_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; 
lean_inc(v_declName_2052_);
v___x_2057_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_2052_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2065_; 
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2057_, 0);
lean_dec(v_unused_2066_);
v___x_2059_ = v___x_2057_;
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v___x_2057_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v_declName_2052_);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_declName_2052_);
v___x_2062_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2051_, v___x_2062_, v_attrKind_2053_, v_a_2054_, v_a_2055_);
return v___x_2063_;
}
}
}
else
{
lean_dec(v_declName_2052_);
lean_dec_ref(v_ext_2051_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_2067_, lean_object* v_declName_2068_, lean_object* v_attrKind_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
uint8_t v_attrKind_boxed_2073_; lean_object* v_res_2074_; 
v_attrKind_boxed_2073_ = lean_unbox(v_attrKind_2069_);
v_res_2074_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2067_, v_declName_2068_, v_attrKind_boxed_2073_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_2075_, lean_object* v_declName_2076_, uint8_t v_attrKind_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_declName_2076_);
v___x_2082_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_2075_, v___x_2081_, v_attrKind_2077_, v_a_2078_, v_a_2079_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_2083_, lean_object* v_declName_2084_, lean_object* v_attrKind_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
uint8_t v_attrKind_boxed_2089_; lean_object* v_res_2090_; 
v_attrKind_boxed_2089_ = lean_unbox(v_attrKind_2085_);
v_res_2090_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2083_, v_declName_2084_, v_attrKind_boxed_2089_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_2091_, lean_object* v_s_2092_){
_start:
{
lean_object* v_casesTypes_2093_; lean_object* v_funCC_2094_; lean_object* v_ematch_2095_; lean_object* v_inj_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_casesTypes_2093_ = lean_ctor_get(v_s_2092_, 0);
v_funCC_2094_ = lean_ctor_get(v_s_2092_, 2);
v_ematch_2095_ = lean_ctor_get(v_s_2092_, 3);
v_inj_2096_ = lean_ctor_get(v_s_2092_, 4);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_s_2092_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_s_2092_, 1);
lean_dec(v_unused_2104_);
v___x_2098_ = v_s_2092_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_inj_2096_);
lean_inc(v_ematch_2095_);
lean_inc(v_funCC_2094_);
lean_inc(v_casesTypes_2093_);
lean_dec(v_s_2092_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v_a_2091_);
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_casesTypes_2093_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_a_2091_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_funCC_2094_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_ematch_2095_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_inj_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_2105_, lean_object* v_declName_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v_ext_2112_; lean_object* v_toEnvExtension_2113_; lean_object* v_env_2114_; lean_object* v_asyncMode_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v_extThms_2118_; lean_object* v___x_2119_; 
v___x_2110_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2111_ = lean_st_ref_get(v_a_2108_);
v_ext_2112_ = lean_ctor_get(v_ext_2105_, 1);
v_toEnvExtension_2113_ = lean_ctor_get(v_ext_2112_, 0);
v_env_2114_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_ref(v_env_2114_);
lean_dec(v___x_2111_);
v_asyncMode_2115_ = lean_ctor_get(v_toEnvExtension_2113_, 2);
v___x_2116_ = 0;
v___x_2117_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2110_, v_ext_2105_, v_env_2114_, v_asyncMode_2115_, v___x_2116_);
v_extThms_2118_ = lean_ctor_get(v___x_2117_, 1);
lean_inc_ref(v_extThms_2118_);
lean_dec(v___x_2117_);
v___x_2119_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_2118_, v_declName_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2150_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2150_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2150_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v_env_2126_; lean_object* v_nextMacroScope_2127_; lean_object* v_ngen_2128_; lean_object* v_auxDeclNGen_2129_; lean_object* v_traceState_2130_; lean_object* v_recordedDeps_2131_; lean_object* v_messages_2132_; lean_object* v_infoState_2133_; lean_object* v_snapshotTasks_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2148_; 
v___f_2124_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_2124_, 0, v_a_2120_);
v___x_2125_ = lean_st_ref_take(v_a_2108_);
v_env_2126_ = lean_ctor_get(v___x_2125_, 0);
v_nextMacroScope_2127_ = lean_ctor_get(v___x_2125_, 1);
v_ngen_2128_ = lean_ctor_get(v___x_2125_, 2);
v_auxDeclNGen_2129_ = lean_ctor_get(v___x_2125_, 3);
v_traceState_2130_ = lean_ctor_get(v___x_2125_, 4);
v_recordedDeps_2131_ = lean_ctor_get(v___x_2125_, 6);
v_messages_2132_ = lean_ctor_get(v___x_2125_, 7);
v_infoState_2133_ = lean_ctor_get(v___x_2125_, 8);
v_snapshotTasks_2134_ = lean_ctor_get(v___x_2125_, 9);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v___x_2125_, 5);
lean_dec(v_unused_2149_);
v___x_2136_ = v___x_2125_;
v_isShared_2137_ = v_isSharedCheck_2148_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snapshotTasks_2134_);
lean_inc(v_infoState_2133_);
lean_inc(v_messages_2132_);
lean_inc(v_recordedDeps_2131_);
lean_inc(v_traceState_2130_);
lean_inc(v_auxDeclNGen_2129_);
lean_inc(v_ngen_2128_);
lean_inc(v_nextMacroScope_2127_);
lean_inc(v_env_2126_);
lean_dec(v___x_2125_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2148_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2105_, v_env_2126_, v___f_2124_);
v___x_2140_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 5, v___x_2140_);
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2142_ = v___x_2136_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_nextMacroScope_2127_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_ngen_2128_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v_auxDeclNGen_2129_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v_traceState_2130_);
lean_ctor_set(v_reuseFailAlloc_2147_, 5, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2147_, 6, v_recordedDeps_2131_);
lean_ctor_set(v_reuseFailAlloc_2147_, 7, v_messages_2132_);
lean_ctor_set(v_reuseFailAlloc_2147_, 8, v_infoState_2133_);
lean_ctor_set(v_reuseFailAlloc_2147_, 9, v_snapshotTasks_2134_);
v___x_2142_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = lean_st_ref_put(v_a_2108_, v___x_2142_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2138_);
v___x_2145_ = v___x_2122_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2138_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_ext_2105_);
v_a_2151_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2119_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2119_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_2159_, lean_object* v_declName_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2159_, v_declName_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_2165_, lean_object* v_s_2166_){
_start:
{
lean_object* v_extThms_2167_; lean_object* v_funCC_2168_; lean_object* v_ematch_2169_; lean_object* v_inj_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_extThms_2167_ = lean_ctor_get(v_s_2166_, 1);
v_funCC_2168_ = lean_ctor_get(v_s_2166_, 2);
v_ematch_2169_ = lean_ctor_get(v_s_2166_, 3);
v_inj_2170_ = lean_ctor_get(v_s_2166_, 4);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_s_2166_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_s_2166_, 0);
lean_dec(v_unused_2178_);
v___x_2172_ = v_s_2166_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_inj_2170_);
lean_inc(v_ematch_2169_);
lean_inc(v_funCC_2168_);
lean_inc(v_extThms_2167_);
lean_dec(v_s_2166_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v_a_2165_);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2165_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_extThms_2167_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_funCC_2168_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_ematch_2169_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_inj_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_2179_, lean_object* v_declName_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_2180_);
v___x_2185_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v___x_2186_; lean_object* v_ext_2187_; lean_object* v_toEnvExtension_2188_; lean_object* v_env_2189_; lean_object* v_asyncMode_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v_casesTypes_2193_; lean_object* v___x_2194_; 
lean_dec_ref_known(v___x_2185_, 1);
v___x_2186_ = lean_st_ref_get(v_a_2182_);
v_ext_2187_ = lean_ctor_get(v_ext_2179_, 1);
v_toEnvExtension_2188_ = lean_ctor_get(v_ext_2187_, 0);
v_env_2189_ = lean_ctor_get(v___x_2186_, 0);
lean_inc_ref(v_env_2189_);
lean_dec(v___x_2186_);
v_asyncMode_2190_ = lean_ctor_get(v_toEnvExtension_2188_, 2);
v___x_2191_ = 0;
v___x_2192_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2184_, v_ext_2179_, v_env_2189_, v_asyncMode_2190_, v___x_2191_);
v_casesTypes_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_ref(v_casesTypes_2193_);
lean_dec(v___x_2192_);
v___x_2194_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_2193_, v_declName_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2225_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2225_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2225_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___f_2199_; lean_object* v___x_2200_; lean_object* v_env_2201_; lean_object* v_nextMacroScope_2202_; lean_object* v_ngen_2203_; lean_object* v_auxDeclNGen_2204_; lean_object* v_traceState_2205_; lean_object* v_recordedDeps_2206_; lean_object* v_messages_2207_; lean_object* v_infoState_2208_; lean_object* v_snapshotTasks_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2223_; 
v___f_2199_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_2199_, 0, v_a_2195_);
v___x_2200_ = lean_st_ref_take(v_a_2182_);
v_env_2201_ = lean_ctor_get(v___x_2200_, 0);
v_nextMacroScope_2202_ = lean_ctor_get(v___x_2200_, 1);
v_ngen_2203_ = lean_ctor_get(v___x_2200_, 2);
v_auxDeclNGen_2204_ = lean_ctor_get(v___x_2200_, 3);
v_traceState_2205_ = lean_ctor_get(v___x_2200_, 4);
v_recordedDeps_2206_ = lean_ctor_get(v___x_2200_, 6);
v_messages_2207_ = lean_ctor_get(v___x_2200_, 7);
v_infoState_2208_ = lean_ctor_get(v___x_2200_, 8);
v_snapshotTasks_2209_ = lean_ctor_get(v___x_2200_, 9);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v___x_2200_, 5);
lean_dec(v_unused_2224_);
v___x_2211_ = v___x_2200_;
v_isShared_2212_ = v_isSharedCheck_2223_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_snapshotTasks_2209_);
lean_inc(v_infoState_2208_);
lean_inc(v_messages_2207_);
lean_inc(v_recordedDeps_2206_);
lean_inc(v_traceState_2205_);
lean_inc(v_auxDeclNGen_2204_);
lean_inc(v_ngen_2203_);
lean_inc(v_nextMacroScope_2202_);
lean_inc(v_env_2201_);
lean_dec(v___x_2200_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2223_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2179_, v_env_2201_, v___f_2199_);
v___x_2215_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 5, v___x_2215_);
lean_ctor_set(v___x_2211_, 0, v___x_2214_);
v___x_2217_ = v___x_2211_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_nextMacroScope_2202_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_ngen_2203_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_auxDeclNGen_2204_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_traceState_2205_);
lean_ctor_set(v_reuseFailAlloc_2222_, 5, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2222_, 6, v_recordedDeps_2206_);
lean_ctor_set(v_reuseFailAlloc_2222_, 7, v_messages_2207_);
lean_ctor_set(v_reuseFailAlloc_2222_, 8, v_infoState_2208_);
lean_ctor_set(v_reuseFailAlloc_2222_, 9, v_snapshotTasks_2209_);
v___x_2217_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_st_ref_put(v_a_2182_, v___x_2217_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2213_);
v___x_2220_ = v___x_2197_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2213_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_ext_2179_);
v_a_2226_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2194_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2194_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_dec(v_declName_2180_);
lean_dec_ref(v_ext_2179_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_2234_, lean_object* v_declName_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2234_, v_declName_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_2240_, lean_object* v_s_2241_){
_start:
{
lean_object* v_casesTypes_2242_; lean_object* v_extThms_2243_; lean_object* v_ematch_2244_; lean_object* v_inj_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
v_casesTypes_2242_ = lean_ctor_get(v_s_2241_, 0);
v_extThms_2243_ = lean_ctor_get(v_s_2241_, 1);
v_ematch_2244_ = lean_ctor_get(v_s_2241_, 3);
v_inj_2245_ = lean_ctor_get(v_s_2241_, 4);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_s_2241_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; 
v_unused_2253_ = lean_ctor_get(v_s_2241_, 2);
lean_dec(v_unused_2253_);
v___x_2247_ = v_s_2241_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_inj_2245_);
lean_inc(v_ematch_2244_);
lean_inc(v_extThms_2243_);
lean_inc(v_casesTypes_2242_);
lean_dec(v_s_2241_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 2, v___x_2240_);
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_casesTypes_2242_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_extThms_2243_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_ematch_2244_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_inj_2245_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_2254_, lean_object* v_t_2255_){
_start:
{
if (lean_obj_tag(v_t_2255_) == 0)
{
lean_object* v_k_2256_; lean_object* v_v_2257_; lean_object* v_l_2258_; lean_object* v_r_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2913_; 
v_k_2256_ = lean_ctor_get(v_t_2255_, 1);
v_v_2257_ = lean_ctor_get(v_t_2255_, 2);
v_l_2258_ = lean_ctor_get(v_t_2255_, 3);
v_r_2259_ = lean_ctor_get(v_t_2255_, 4);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_t_2255_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v_t_2255_, 0);
lean_dec(v_unused_2914_);
v___x_2261_ = v_t_2255_;
v_isShared_2262_ = v_isSharedCheck_2913_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_r_2259_);
lean_inc(v_l_2258_);
lean_inc(v_v_2257_);
lean_inc(v_k_2256_);
lean_dec(v_t_2255_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2913_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
uint8_t v___x_2263_; 
v___x_2263_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2254_, v_k_2256_);
switch(v___x_2263_)
{
case 0:
{
lean_object* v_impl_2264_; lean_object* v___x_2265_; 
v_impl_2264_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2254_, v_l_2258_);
v___x_2265_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2264_) == 0)
{
if (lean_obj_tag(v_r_2259_) == 0)
{
lean_object* v_size_2266_; lean_object* v_size_2267_; lean_object* v_k_2268_; lean_object* v_v_2269_; lean_object* v_l_2270_; lean_object* v_r_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_size_2266_ = lean_ctor_get(v_impl_2264_, 0);
v_size_2267_ = lean_ctor_get(v_r_2259_, 0);
v_k_2268_ = lean_ctor_get(v_r_2259_, 1);
v_v_2269_ = lean_ctor_get(v_r_2259_, 2);
v_l_2270_ = lean_ctor_get(v_r_2259_, 3);
lean_inc(v_l_2270_);
v_r_2271_ = lean_ctor_get(v_r_2259_, 4);
v___x_2272_ = lean_unsigned_to_nat(3u);
v___x_2273_ = lean_nat_mul(v___x_2272_, v_size_2266_);
v___x_2274_ = lean_nat_dec_lt(v___x_2273_, v_size_2267_);
lean_dec(v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_dec(v_l_2270_);
v___x_2275_ = lean_nat_add(v___x_2265_, v_size_2266_);
v___x_2276_ = lean_nat_add(v___x_2275_, v_size_2267_);
lean_dec(v___x_2275_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 3, v_impl_2264_);
lean_ctor_set(v___x_2261_, 0, v___x_2276_);
v___x_2278_ = v___x_2261_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_impl_2264_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_r_2259_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
else
{
lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2343_; 
lean_inc(v_r_2271_);
lean_inc(v_v_2269_);
lean_inc(v_k_2268_);
lean_inc(v_size_2267_);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; lean_object* v_unused_2345_; lean_object* v_unused_2346_; lean_object* v_unused_2347_; lean_object* v_unused_2348_; 
v_unused_2344_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2345_);
v_unused_2346_ = lean_ctor_get(v_r_2259_, 2);
lean_dec(v_unused_2346_);
v_unused_2347_ = lean_ctor_get(v_r_2259_, 1);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_r_2259_, 0);
lean_dec(v_unused_2348_);
v___x_2281_ = v_r_2259_;
v_isShared_2282_ = v_isSharedCheck_2343_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v_r_2259_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2343_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_size_2283_; lean_object* v_k_2284_; lean_object* v_v_2285_; lean_object* v_l_2286_; lean_object* v_r_2287_; lean_object* v_size_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_size_2283_ = lean_ctor_get(v_l_2270_, 0);
v_k_2284_ = lean_ctor_get(v_l_2270_, 1);
v_v_2285_ = lean_ctor_get(v_l_2270_, 2);
v_l_2286_ = lean_ctor_get(v_l_2270_, 3);
v_r_2287_ = lean_ctor_get(v_l_2270_, 4);
v_size_2288_ = lean_ctor_get(v_r_2271_, 0);
v___x_2289_ = lean_unsigned_to_nat(2u);
v___x_2290_ = lean_nat_mul(v___x_2289_, v_size_2288_);
v___x_2291_ = lean_nat_dec_lt(v_size_2283_, v___x_2290_);
lean_dec(v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2319_; 
lean_inc(v_r_2287_);
lean_inc(v_l_2286_);
lean_inc(v_v_2285_);
lean_inc(v_k_2284_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_l_2270_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2320_ = lean_ctor_get(v_l_2270_, 4);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_l_2270_, 3);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_l_2270_, 2);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_l_2270_, 1);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_l_2270_, 0);
lean_dec(v_unused_2324_);
v___x_2293_ = v_l_2270_;
v_isShared_2294_ = v_isSharedCheck_2319_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v_l_2270_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2319_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2309_; 
v___x_2295_ = lean_nat_add(v___x_2265_, v_size_2266_);
v___x_2296_ = lean_nat_add(v___x_2295_, v_size_2267_);
lean_dec(v_size_2267_);
if (lean_obj_tag(v_l_2286_) == 0)
{
lean_object* v_size_2317_; 
v_size_2317_ = lean_ctor_get(v_l_2286_, 0);
lean_inc(v_size_2317_);
v___y_2309_ = v_size_2317_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_unsigned_to_nat(0u);
v___y_2309_ = v___x_2318_;
goto v___jp_2308_;
}
v___jp_2297_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_nat_add(v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec(v___y_2299_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 4, v_r_2271_);
lean_ctor_set(v___x_2293_, 3, v_r_2287_);
lean_ctor_set(v___x_2293_, 2, v_v_2269_);
lean_ctor_set(v___x_2293_, 1, v_k_2268_);
lean_ctor_set(v___x_2293_, 0, v___x_2301_);
v___x_2303_ = v___x_2293_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_k_2268_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_v_2269_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_r_2287_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_r_2271_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 4, v___x_2303_);
lean_ctor_set(v___x_2281_, 3, v___y_2298_);
lean_ctor_set(v___x_2281_, 2, v_v_2285_);
lean_ctor_set(v___x_2281_, 1, v_k_2284_);
lean_ctor_set(v___x_2281_, 0, v___x_2296_);
v___x_2305_ = v___x_2281_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_k_2284_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_v_2285_);
lean_ctor_set(v_reuseFailAlloc_2306_, 3, v___y_2298_);
lean_ctor_set(v_reuseFailAlloc_2306_, 4, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
v___jp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = lean_nat_add(v___x_2295_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec(v___x_2295_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_l_2286_);
lean_ctor_set(v___x_2261_, 3, v_impl_2264_);
lean_ctor_set(v___x_2261_, 0, v___x_2310_);
v___x_2312_ = v___x_2261_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v_impl_2264_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v_l_2286_);
v___x_2312_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_nat_add(v___x_2265_, v_size_2288_);
if (lean_obj_tag(v_r_2287_) == 0)
{
lean_object* v_size_2314_; 
v_size_2314_ = lean_ctor_get(v_r_2287_, 0);
lean_inc(v_size_2314_);
v___y_2298_ = v___x_2312_;
v___y_2299_ = v___x_2313_;
v___y_2300_ = v_size_2314_;
goto v___jp_2297_;
}
else
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v___y_2298_ = v___x_2312_;
v___y_2299_ = v___x_2313_;
v___y_2300_ = v___x_2315_;
goto v___jp_2297_;
}
}
}
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_del_object(v___x_2261_);
v___x_2325_ = lean_nat_add(v___x_2265_, v_size_2266_);
v___x_2326_ = lean_nat_add(v___x_2325_, v_size_2267_);
lean_dec(v_size_2267_);
v___x_2327_ = lean_nat_add(v___x_2325_, v_size_2283_);
lean_dec(v___x_2325_);
lean_inc_ref(v_impl_2264_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 4, v_l_2270_);
lean_ctor_set(v___x_2281_, 3, v_impl_2264_);
lean_ctor_set(v___x_2281_, 2, v_v_2257_);
lean_ctor_set(v___x_2281_, 1, v_k_2256_);
lean_ctor_set(v___x_2281_, 0, v___x_2327_);
v___x_2329_ = v___x_2281_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2342_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2342_, 3, v_impl_2264_);
lean_ctor_set(v_reuseFailAlloc_2342_, 4, v_l_2270_);
v___x_2329_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
v_isSharedCheck_2336_ = !lean_is_exclusive(v_impl_2264_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; lean_object* v_unused_2338_; lean_object* v_unused_2339_; lean_object* v_unused_2340_; lean_object* v_unused_2341_; 
v_unused_2337_ = lean_ctor_get(v_impl_2264_, 4);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_impl_2264_, 3);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_impl_2264_, 2);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_impl_2264_, 1);
lean_dec(v_unused_2340_);
v_unused_2341_ = lean_ctor_get(v_impl_2264_, 0);
lean_dec(v_unused_2341_);
v___x_2331_ = v_impl_2264_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_dec(v_impl_2264_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 4, v_r_2271_);
lean_ctor_set(v___x_2331_, 3, v___x_2329_);
lean_ctor_set(v___x_2331_, 2, v_v_2269_);
lean_ctor_set(v___x_2331_, 1, v_k_2268_);
lean_ctor_set(v___x_2331_, 0, v___x_2326_);
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2268_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2269_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_r_2271_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v_size_2349_ = lean_ctor_get(v_impl_2264_, 0);
v___x_2350_ = lean_nat_add(v___x_2265_, v_size_2349_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 3, v_impl_2264_);
lean_ctor_set(v___x_2261_, 0, v___x_2350_);
v___x_2352_ = v___x_2261_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_impl_2264_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v_r_2259_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
else
{
if (lean_obj_tag(v_r_2259_) == 0)
{
lean_object* v_l_2354_; 
v_l_2354_ = lean_ctor_get(v_r_2259_, 3);
lean_inc(v_l_2354_);
if (lean_obj_tag(v_l_2354_) == 0)
{
lean_object* v_r_2355_; 
v_r_2355_ = lean_ctor_get(v_r_2259_, 4);
lean_inc(v_r_2355_);
if (lean_obj_tag(v_r_2355_) == 0)
{
lean_object* v_size_2356_; lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2371_; 
v_size_2356_ = lean_ctor_get(v_r_2259_, 0);
v_k_2357_ = lean_ctor_get(v_r_2259_, 1);
v_v_2358_ = lean_ctor_get(v_r_2259_, 2);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2371_ == 0)
{
lean_object* v_unused_2372_; lean_object* v_unused_2373_; 
v_unused_2372_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2373_);
v___x_2360_ = v_r_2259_;
v_isShared_2361_ = v_isSharedCheck_2371_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_v_2358_);
lean_inc(v_k_2357_);
lean_inc(v_size_2356_);
lean_dec(v_r_2259_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2371_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_size_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v_size_2362_ = lean_ctor_get(v_l_2354_, 0);
v___x_2363_ = lean_nat_add(v___x_2265_, v_size_2356_);
lean_dec(v_size_2356_);
v___x_2364_ = lean_nat_add(v___x_2265_, v_size_2362_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 4, v_l_2354_);
lean_ctor_set(v___x_2360_, 3, v_impl_2264_);
lean_ctor_set(v___x_2360_, 2, v_v_2257_);
lean_ctor_set(v___x_2360_, 1, v_k_2256_);
lean_ctor_set(v___x_2360_, 0, v___x_2364_);
v___x_2366_ = v___x_2360_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_impl_2264_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_l_2354_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_r_2355_);
lean_ctor_set(v___x_2261_, 3, v___x_2366_);
lean_ctor_set(v___x_2261_, 2, v_v_2358_);
lean_ctor_set(v___x_2261_, 1, v_k_2357_);
lean_ctor_set(v___x_2261_, 0, v___x_2363_);
v___x_2368_ = v___x_2261_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_k_2357_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_v_2358_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v_r_2355_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_k_2374_; lean_object* v_v_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2398_; 
v_k_2374_ = lean_ctor_get(v_r_2259_, 1);
v_v_2375_ = lean_ctor_get(v_r_2259_, 2);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; lean_object* v_unused_2400_; lean_object* v_unused_2401_; 
v_unused_2399_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_r_2259_, 0);
lean_dec(v_unused_2401_);
v___x_2377_ = v_r_2259_;
v_isShared_2378_ = v_isSharedCheck_2398_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_v_2375_);
lean_inc(v_k_2374_);
lean_dec(v_r_2259_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2398_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v_k_2379_; lean_object* v_v_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2394_; 
v_k_2379_ = lean_ctor_get(v_l_2354_, 1);
v_v_2380_ = lean_ctor_get(v_l_2354_, 2);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_l_2354_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; lean_object* v_unused_2396_; lean_object* v_unused_2397_; 
v_unused_2395_ = lean_ctor_get(v_l_2354_, 4);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_l_2354_, 3);
lean_dec(v_unused_2396_);
v_unused_2397_ = lean_ctor_get(v_l_2354_, 0);
lean_dec(v_unused_2397_);
v___x_2382_ = v_l_2354_;
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_v_2380_);
lean_inc(v_k_2379_);
lean_dec(v_l_2354_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_unsigned_to_nat(3u);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_r_2355_);
lean_ctor_set(v___x_2382_, 3, v_r_2355_);
lean_ctor_set(v___x_2382_, 2, v_v_2257_);
lean_ctor_set(v___x_2382_, 1, v_k_2256_);
lean_ctor_set(v___x_2382_, 0, v___x_2265_);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_r_2355_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v_r_2355_);
v___x_2386_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2388_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 3, v_r_2355_);
lean_ctor_set(v___x_2377_, 0, v___x_2265_);
v___x_2388_ = v___x_2377_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_k_2374_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_v_2375_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_r_2355_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_r_2355_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v___x_2388_);
lean_ctor_set(v___x_2261_, 3, v___x_2386_);
lean_ctor_set(v___x_2261_, 2, v_v_2380_);
lean_ctor_set(v___x_2261_, 1, v_k_2379_);
lean_ctor_set(v___x_2261_, 0, v___x_2384_);
v___x_2390_ = v___x_2261_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_k_2379_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_v_2380_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2402_; 
v_r_2402_ = lean_ctor_get(v_r_2259_, 4);
lean_inc(v_r_2402_);
if (lean_obj_tag(v_r_2402_) == 0)
{
lean_object* v_k_2403_; lean_object* v_v_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2415_; 
v_k_2403_ = lean_ctor_get(v_r_2259_, 1);
v_v_2404_ = lean_ctor_get(v_r_2259_, 2);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2416_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_r_2259_, 0);
lean_dec(v_unused_2418_);
v___x_2406_ = v_r_2259_;
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_v_2404_);
lean_inc(v_k_2403_);
lean_dec(v_r_2259_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2415_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = lean_unsigned_to_nat(3u);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_l_2354_);
lean_ctor_set(v___x_2406_, 2, v_v_2257_);
lean_ctor_set(v___x_2406_, 1, v_k_2256_);
lean_ctor_set(v___x_2406_, 0, v___x_2265_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_l_2354_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v_l_2354_);
v___x_2410_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2412_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_r_2402_);
lean_ctor_set(v___x_2261_, 3, v___x_2410_);
lean_ctor_set(v___x_2261_, 2, v_v_2404_);
lean_ctor_set(v___x_2261_, 1, v_k_2403_);
lean_ctor_set(v___x_2261_, 0, v___x_2408_);
v___x_2412_ = v___x_2261_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_r_2402_);
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
else
{
lean_object* v_size_2419_; lean_object* v_k_2420_; lean_object* v_v_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2432_; 
v_size_2419_ = lean_ctor_get(v_r_2259_, 0);
v_k_2420_ = lean_ctor_get(v_r_2259_, 1);
v_v_2421_ = lean_ctor_get(v_r_2259_, 2);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; lean_object* v_unused_2434_; 
v_unused_2433_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2433_);
v_unused_2434_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2434_);
v___x_2423_ = v_r_2259_;
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_v_2421_);
lean_inc(v_k_2420_);
lean_inc(v_size_2419_);
lean_dec(v_r_2259_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 3, v_r_2402_);
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_size_2419_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_k_2420_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_v_2421_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_r_2402_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_r_2402_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_unsigned_to_nat(2u);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v___x_2426_);
lean_ctor_set(v___x_2261_, 3, v_r_2402_);
lean_ctor_set(v___x_2261_, 0, v___x_2427_);
v___x_2429_ = v___x_2261_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_r_2402_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v___x_2426_);
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
}
}
else
{
lean_object* v___x_2436_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 3, v_r_2259_);
lean_ctor_set(v___x_2261_, 0, v___x_2265_);
v___x_2436_ = v___x_2261_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_r_2259_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_r_2259_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2261_);
lean_dec(v_v_2257_);
lean_dec(v_k_2256_);
if (lean_obj_tag(v_l_2258_) == 0)
{
if (lean_obj_tag(v_r_2259_) == 0)
{
lean_object* v_size_2438_; lean_object* v_k_2439_; lean_object* v_v_2440_; lean_object* v_l_2441_; lean_object* v_r_2442_; lean_object* v_size_2443_; lean_object* v_k_2444_; lean_object* v_v_2445_; lean_object* v_l_2446_; lean_object* v_r_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v_size_2438_ = lean_ctor_get(v_l_2258_, 0);
v_k_2439_ = lean_ctor_get(v_l_2258_, 1);
v_v_2440_ = lean_ctor_get(v_l_2258_, 2);
v_l_2441_ = lean_ctor_get(v_l_2258_, 3);
v_r_2442_ = lean_ctor_get(v_l_2258_, 4);
lean_inc(v_r_2442_);
v_size_2443_ = lean_ctor_get(v_r_2259_, 0);
v_k_2444_ = lean_ctor_get(v_r_2259_, 1);
v_v_2445_ = lean_ctor_get(v_r_2259_, 2);
v_l_2446_ = lean_ctor_get(v_r_2259_, 3);
lean_inc(v_l_2446_);
v_r_2447_ = lean_ctor_get(v_r_2259_, 4);
v___x_2448_ = lean_unsigned_to_nat(1u);
v___x_2449_ = lean_nat_dec_lt(v_size_2438_, v_size_2443_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2585_; 
lean_inc(v_l_2441_);
lean_inc(v_v_2440_);
lean_inc(v_k_2439_);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; 
v_unused_2586_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_l_2258_, 2);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_l_2258_, 1);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v_l_2258_, 0);
lean_dec(v_unused_2590_);
v___x_2451_ = v_l_2258_;
v_isShared_2452_ = v_isSharedCheck_2585_;
goto v_resetjp_2450_;
}
else
{
lean_dec(v_l_2258_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2585_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v_tree_2454_; 
v___x_2453_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2439_, v_v_2440_, v_l_2441_, v_r_2442_);
v_tree_2454_ = lean_ctor_get(v___x_2453_, 2);
if (lean_obj_tag(v_tree_2454_) == 0)
{
lean_object* v_k_2455_; lean_object* v_v_2456_; lean_object* v_size_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
lean_inc_ref(v_tree_2454_);
v_k_2455_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_k_2455_);
v_v_2456_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_v_2456_);
lean_dec_ref(v___x_2453_);
v_size_2457_ = lean_ctor_get(v_tree_2454_, 0);
v___x_2458_ = lean_unsigned_to_nat(3u);
v___x_2459_ = lean_nat_mul(v___x_2458_, v_size_2457_);
v___x_2460_ = lean_nat_dec_lt(v___x_2459_, v_size_2443_);
lean_dec(v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_dec(v_l_2446_);
v___x_2461_ = lean_nat_add(v___x_2448_, v_size_2457_);
v___x_2462_ = lean_nat_add(v___x_2461_, v_size_2443_);
lean_dec(v___x_2461_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v_r_2259_);
lean_ctor_set(v___x_2451_, 3, v_tree_2454_);
lean_ctor_set(v___x_2451_, 2, v_v_2456_);
lean_ctor_set(v___x_2451_, 1, v_k_2455_);
lean_ctor_set(v___x_2451_, 0, v___x_2462_);
v___x_2464_ = v___x_2451_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_k_2455_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_v_2456_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_tree_2454_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v_r_2259_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
else
{
lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2520_; 
lean_inc(v_r_2447_);
lean_inc(v_v_2445_);
lean_inc(v_k_2444_);
lean_inc(v_size_2443_);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; lean_object* v_unused_2522_; lean_object* v_unused_2523_; lean_object* v_unused_2524_; lean_object* v_unused_2525_; 
v_unused_2521_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2521_);
v_unused_2522_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2522_);
v_unused_2523_ = lean_ctor_get(v_r_2259_, 2);
lean_dec(v_unused_2523_);
v_unused_2524_ = lean_ctor_get(v_r_2259_, 1);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_r_2259_, 0);
lean_dec(v_unused_2525_);
v___x_2467_ = v_r_2259_;
v_isShared_2468_ = v_isSharedCheck_2520_;
goto v_resetjp_2466_;
}
else
{
lean_dec(v_r_2259_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2520_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_size_2469_; lean_object* v_k_2470_; lean_object* v_v_2471_; lean_object* v_l_2472_; lean_object* v_r_2473_; lean_object* v_size_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v_size_2469_ = lean_ctor_get(v_l_2446_, 0);
v_k_2470_ = lean_ctor_get(v_l_2446_, 1);
v_v_2471_ = lean_ctor_get(v_l_2446_, 2);
v_l_2472_ = lean_ctor_get(v_l_2446_, 3);
v_r_2473_ = lean_ctor_get(v_l_2446_, 4);
v_size_2474_ = lean_ctor_get(v_r_2447_, 0);
v___x_2475_ = lean_unsigned_to_nat(2u);
v___x_2476_ = lean_nat_mul(v___x_2475_, v_size_2474_);
v___x_2477_ = lean_nat_dec_lt(v_size_2469_, v___x_2476_);
lean_dec(v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2505_; 
lean_inc(v_r_2473_);
lean_inc(v_l_2472_);
lean_inc(v_v_2471_);
lean_inc(v_k_2470_);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_l_2446_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; lean_object* v_unused_2509_; lean_object* v_unused_2510_; 
v_unused_2506_ = lean_ctor_get(v_l_2446_, 4);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_l_2446_, 3);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_l_2446_, 2);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_l_2446_, 1);
lean_dec(v_unused_2509_);
v_unused_2510_ = lean_ctor_get(v_l_2446_, 0);
lean_dec(v_unused_2510_);
v___x_2479_ = v_l_2446_;
v_isShared_2480_ = v_isSharedCheck_2505_;
goto v_resetjp_2478_;
}
else
{
lean_dec(v_l_2446_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2505_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2495_; 
v___x_2481_ = lean_nat_add(v___x_2448_, v_size_2457_);
v___x_2482_ = lean_nat_add(v___x_2481_, v_size_2443_);
lean_dec(v_size_2443_);
if (lean_obj_tag(v_l_2472_) == 0)
{
lean_object* v_size_2503_; 
v_size_2503_ = lean_ctor_get(v_l_2472_, 0);
lean_inc(v_size_2503_);
v___y_2495_ = v_size_2503_;
goto v___jp_2494_;
}
else
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_unsigned_to_nat(0u);
v___y_2495_ = v___x_2504_;
goto v___jp_2494_;
}
v___jp_2483_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = lean_nat_add(v___y_2484_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec(v___y_2484_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_r_2447_);
lean_ctor_set(v___x_2479_, 3, v_r_2473_);
lean_ctor_set(v___x_2479_, 2, v_v_2445_);
lean_ctor_set(v___x_2479_, 1, v_k_2444_);
lean_ctor_set(v___x_2479_, 0, v___x_2487_);
v___x_2489_ = v___x_2479_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_k_2444_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_v_2445_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_r_2473_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_r_2447_);
v___x_2489_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 4, v___x_2489_);
lean_ctor_set(v___x_2467_, 3, v___y_2485_);
lean_ctor_set(v___x_2467_, 2, v_v_2471_);
lean_ctor_set(v___x_2467_, 1, v_k_2470_);
lean_ctor_set(v___x_2467_, 0, v___x_2482_);
v___x_2491_ = v___x_2467_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_k_2470_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_v_2471_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v___y_2485_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
v___jp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2496_ = lean_nat_add(v___x_2481_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec(v___x_2481_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v_l_2472_);
lean_ctor_set(v___x_2451_, 3, v_tree_2454_);
lean_ctor_set(v___x_2451_, 2, v_v_2456_);
lean_ctor_set(v___x_2451_, 1, v_k_2455_);
lean_ctor_set(v___x_2451_, 0, v___x_2496_);
v___x_2498_ = v___x_2451_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_k_2455_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_v_2456_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_tree_2454_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_l_2472_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_nat_add(v___x_2448_, v_size_2474_);
if (lean_obj_tag(v_r_2473_) == 0)
{
lean_object* v_size_2500_; 
v_size_2500_ = lean_ctor_get(v_r_2473_, 0);
lean_inc(v_size_2500_);
v___y_2484_ = v___x_2499_;
v___y_2485_ = v___x_2498_;
v___y_2486_ = v_size_2500_;
goto v___jp_2483_;
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_unsigned_to_nat(0u);
v___y_2484_ = v___x_2499_;
v___y_2485_ = v___x_2498_;
v___y_2486_ = v___x_2501_;
goto v___jp_2483_;
}
}
}
}
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2511_ = lean_nat_add(v___x_2448_, v_size_2457_);
v___x_2512_ = lean_nat_add(v___x_2511_, v_size_2443_);
lean_dec(v_size_2443_);
v___x_2513_ = lean_nat_add(v___x_2511_, v_size_2469_);
lean_dec(v___x_2511_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 4, v_l_2446_);
lean_ctor_set(v___x_2467_, 3, v_tree_2454_);
lean_ctor_set(v___x_2467_, 2, v_v_2456_);
lean_ctor_set(v___x_2467_, 1, v_k_2455_);
lean_ctor_set(v___x_2467_, 0, v___x_2513_);
v___x_2515_ = v___x_2467_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_k_2455_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_v_2456_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_tree_2454_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_l_2446_);
v___x_2515_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2517_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v_r_2447_);
lean_ctor_set(v___x_2451_, 3, v___x_2515_);
lean_ctor_set(v___x_2451_, 2, v_v_2445_);
lean_ctor_set(v___x_2451_, 1, v_k_2444_);
lean_ctor_set(v___x_2451_, 0, v___x_2512_);
v___x_2517_ = v___x_2451_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_k_2444_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_v_2445_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_r_2447_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
}
else
{
lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2579_; 
lean_inc(v_r_2447_);
lean_inc(v_v_2445_);
lean_inc(v_k_2444_);
lean_inc(v_size_2443_);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; lean_object* v_unused_2584_; 
v_unused_2580_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2580_);
v_unused_2581_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_r_2259_, 2);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_r_2259_, 1);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_r_2259_, 0);
lean_dec(v_unused_2584_);
v___x_2527_ = v_r_2259_;
v_isShared_2528_ = v_isSharedCheck_2579_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v_r_2259_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2579_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
if (lean_obj_tag(v_l_2446_) == 0)
{
if (lean_obj_tag(v_r_2447_) == 0)
{
lean_object* v_k_2529_; lean_object* v_v_2530_; lean_object* v_size_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
lean_inc(v_tree_2454_);
v_k_2529_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_k_2529_);
v_v_2530_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_v_2530_);
lean_dec_ref(v___x_2453_);
v_size_2531_ = lean_ctor_get(v_l_2446_, 0);
v___x_2532_ = lean_nat_add(v___x_2448_, v_size_2443_);
lean_dec(v_size_2443_);
v___x_2533_ = lean_nat_add(v___x_2448_, v_size_2531_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 4, v_l_2446_);
lean_ctor_set(v___x_2527_, 3, v_tree_2454_);
lean_ctor_set(v___x_2527_, 2, v_v_2530_);
lean_ctor_set(v___x_2527_, 1, v_k_2529_);
lean_ctor_set(v___x_2527_, 0, v___x_2533_);
v___x_2535_ = v___x_2527_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2529_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2530_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_tree_2454_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_l_2446_);
v___x_2535_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2537_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v_r_2447_);
lean_ctor_set(v___x_2451_, 3, v___x_2535_);
lean_ctor_set(v___x_2451_, 2, v_v_2445_);
lean_ctor_set(v___x_2451_, 1, v_k_2444_);
lean_ctor_set(v___x_2451_, 0, v___x_2532_);
v___x_2537_ = v___x_2451_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_k_2444_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_v_2445_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v_r_2447_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_k_2540_; lean_object* v_v_2541_; lean_object* v_k_2542_; lean_object* v_v_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v_size_2443_);
v_k_2540_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_k_2540_);
v_v_2541_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_v_2541_);
lean_dec_ref(v___x_2453_);
v_k_2542_ = lean_ctor_get(v_l_2446_, 1);
v_v_2543_ = lean_ctor_get(v_l_2446_, 2);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_l_2446_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; 
v_unused_2558_ = lean_ctor_get(v_l_2446_, 4);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_l_2446_, 3);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_l_2446_, 0);
lean_dec(v_unused_2560_);
v___x_2545_ = v_l_2446_;
v_isShared_2546_ = v_isSharedCheck_2557_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_v_2543_);
lean_inc(v_k_2542_);
lean_dec(v_l_2446_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2557_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2547_ = lean_unsigned_to_nat(3u);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_r_2447_);
lean_ctor_set(v___x_2545_, 3, v_r_2447_);
lean_ctor_set(v___x_2545_, 2, v_v_2541_);
lean_ctor_set(v___x_2545_, 1, v_k_2540_);
lean_ctor_set(v___x_2545_, 0, v___x_2448_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_k_2540_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_v_2541_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_r_2447_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v_r_2447_);
v___x_2549_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 3, v_r_2447_);
lean_ctor_set(v___x_2527_, 0, v___x_2448_);
v___x_2551_ = v___x_2527_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_k_2444_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_v_2445_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_r_2447_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_r_2447_);
v___x_2551_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2553_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v___x_2551_);
lean_ctor_set(v___x_2451_, 3, v___x_2549_);
lean_ctor_set(v___x_2451_, 2, v_v_2543_);
lean_ctor_set(v___x_2451_, 1, v_k_2542_);
lean_ctor_set(v___x_2451_, 0, v___x_2547_);
v___x_2553_ = v___x_2451_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_k_2542_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_v_2543_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2447_) == 0)
{
lean_object* v_k_2561_; lean_object* v_v_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_dec(v_size_2443_);
v_k_2561_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_k_2561_);
v_v_2562_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_v_2562_);
lean_dec_ref(v___x_2453_);
v___x_2563_ = lean_unsigned_to_nat(3u);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 4, v_l_2446_);
lean_ctor_set(v___x_2527_, 2, v_v_2562_);
lean_ctor_set(v___x_2527_, 1, v_k_2561_);
lean_ctor_set(v___x_2527_, 0, v___x_2448_);
v___x_2565_ = v___x_2527_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_k_2561_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_v_2562_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_l_2446_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_l_2446_);
v___x_2565_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2567_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v_r_2447_);
lean_ctor_set(v___x_2451_, 3, v___x_2565_);
lean_ctor_set(v___x_2451_, 2, v_v_2445_);
lean_ctor_set(v___x_2451_, 1, v_k_2444_);
lean_ctor_set(v___x_2451_, 0, v___x_2563_);
v___x_2567_ = v___x_2451_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_k_2444_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_v_2445_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_r_2447_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v_k_2570_; lean_object* v_v_2571_; lean_object* v___x_2573_; 
v_k_2570_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_k_2570_);
v_v_2571_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_v_2571_);
lean_dec_ref(v___x_2453_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 3, v_r_2447_);
v___x_2573_ = v___x_2527_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_size_2443_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_k_2444_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_v_2445_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_r_2447_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_r_2447_);
v___x_2573_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_unsigned_to_nat(2u);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v___x_2573_);
lean_ctor_set(v___x_2451_, 3, v_r_2447_);
lean_ctor_set(v___x_2451_, 2, v_v_2571_);
lean_ctor_set(v___x_2451_, 1, v_k_2570_);
lean_ctor_set(v___x_2451_, 0, v___x_2574_);
v___x_2576_ = v___x_2451_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_r_2447_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v___x_2573_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
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
lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2743_; 
lean_inc(v_r_2447_);
lean_inc(v_v_2445_);
lean_inc(v_k_2444_);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_r_2259_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; 
v_unused_2744_ = lean_ctor_get(v_r_2259_, 4);
lean_dec(v_unused_2744_);
v_unused_2745_ = lean_ctor_get(v_r_2259_, 3);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_r_2259_, 2);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_r_2259_, 1);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_r_2259_, 0);
lean_dec(v_unused_2748_);
v___x_2592_ = v_r_2259_;
v_isShared_2593_ = v_isSharedCheck_2743_;
goto v_resetjp_2591_;
}
else
{
lean_dec(v_r_2259_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2743_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v_tree_2595_; 
v___x_2594_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2444_, v_v_2445_, v_l_2446_, v_r_2447_);
v_tree_2595_ = lean_ctor_get(v___x_2594_, 2);
lean_inc(v_tree_2595_);
if (lean_obj_tag(v_tree_2595_) == 0)
{
lean_object* v_k_2596_; lean_object* v_v_2597_; lean_object* v_size_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_k_2596_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_k_2596_);
v_v_2597_ = lean_ctor_get(v___x_2594_, 1);
lean_inc(v_v_2597_);
lean_dec_ref(v___x_2594_);
v_size_2598_ = lean_ctor_get(v_tree_2595_, 0);
v___x_2599_ = lean_unsigned_to_nat(3u);
v___x_2600_ = lean_nat_mul(v___x_2599_, v_size_2598_);
v___x_2601_ = lean_nat_dec_lt(v___x_2600_, v_size_2438_);
lean_dec(v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_dec(v_r_2442_);
v___x_2602_ = lean_nat_add(v___x_2448_, v_size_2438_);
v___x_2603_ = lean_nat_add(v___x_2602_, v_size_2598_);
lean_dec(v___x_2602_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_tree_2595_);
lean_ctor_set(v___x_2592_, 3, v_l_2258_);
lean_ctor_set(v___x_2592_, 2, v_v_2597_);
lean_ctor_set(v___x_2592_, 1, v_k_2596_);
lean_ctor_set(v___x_2592_, 0, v___x_2603_);
v___x_2605_ = v___x_2592_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_k_2596_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_v_2597_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v_tree_2595_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
else
{
lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2672_; 
lean_inc(v_l_2441_);
lean_inc(v_v_2440_);
lean_inc(v_k_2439_);
lean_inc(v_size_2438_);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; lean_object* v_unused_2674_; lean_object* v_unused_2675_; lean_object* v_unused_2676_; lean_object* v_unused_2677_; 
v_unused_2673_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_l_2258_, 2);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_l_2258_, 1);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_l_2258_, 0);
lean_dec(v_unused_2677_);
v___x_2608_ = v_l_2258_;
v_isShared_2609_ = v_isSharedCheck_2672_;
goto v_resetjp_2607_;
}
else
{
lean_dec(v_l_2258_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2672_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_size_2610_; lean_object* v_size_2611_; lean_object* v_k_2612_; lean_object* v_v_2613_; lean_object* v_l_2614_; lean_object* v_r_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_size_2610_ = lean_ctor_get(v_l_2441_, 0);
v_size_2611_ = lean_ctor_get(v_r_2442_, 0);
v_k_2612_ = lean_ctor_get(v_r_2442_, 1);
v_v_2613_ = lean_ctor_get(v_r_2442_, 2);
v_l_2614_ = lean_ctor_get(v_r_2442_, 3);
v_r_2615_ = lean_ctor_get(v_r_2442_, 4);
v___x_2616_ = lean_unsigned_to_nat(2u);
v___x_2617_ = lean_nat_mul(v___x_2616_, v_size_2610_);
v___x_2618_ = lean_nat_dec_lt(v_size_2611_, v___x_2617_);
lean_dec(v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2656_; 
lean_inc(v_r_2615_);
lean_inc(v_l_2614_);
lean_inc(v_v_2613_);
lean_inc(v_k_2612_);
lean_del_object(v___x_2608_);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_r_2442_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; lean_object* v_unused_2658_; lean_object* v_unused_2659_; lean_object* v_unused_2660_; lean_object* v_unused_2661_; 
v_unused_2657_ = lean_ctor_get(v_r_2442_, 4);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_r_2442_, 3);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_r_2442_, 2);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_r_2442_, 1);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_r_2442_, 0);
lean_dec(v_unused_2661_);
v___x_2620_ = v_r_2442_;
v_isShared_2621_ = v_isSharedCheck_2656_;
goto v_resetjp_2619_;
}
else
{
lean_dec(v_r_2442_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2656_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___x_2644_; lean_object* v___y_2646_; 
v___x_2622_ = lean_nat_add(v___x_2448_, v_size_2438_);
lean_dec(v_size_2438_);
v___x_2623_ = lean_nat_add(v___x_2622_, v_size_2598_);
lean_dec(v___x_2622_);
v___x_2644_ = lean_nat_add(v___x_2448_, v_size_2610_);
if (lean_obj_tag(v_l_2614_) == 0)
{
lean_object* v_size_2654_; 
v_size_2654_ = lean_ctor_get(v_l_2614_, 0);
lean_inc(v_size_2654_);
v___y_2646_ = v_size_2654_;
goto v___jp_2645_;
}
else
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_unsigned_to_nat(0u);
v___y_2646_ = v___x_2655_;
goto v___jp_2645_;
}
v___jp_2624_:
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2628_ = lean_nat_add(v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec(v___y_2626_);
lean_inc_ref(v_tree_2595_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 4, v_tree_2595_);
lean_ctor_set(v___x_2620_, 3, v_r_2615_);
lean_ctor_set(v___x_2620_, 2, v_v_2597_);
lean_ctor_set(v___x_2620_, 1, v_k_2596_);
lean_ctor_set(v___x_2620_, 0, v___x_2628_);
v___x_2630_ = v___x_2620_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_k_2596_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_v_2597_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_r_2615_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_tree_2595_);
v___x_2630_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
v_isSharedCheck_2637_ = !lean_is_exclusive(v_tree_2595_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; lean_object* v_unused_2639_; lean_object* v_unused_2640_; lean_object* v_unused_2641_; lean_object* v_unused_2642_; 
v_unused_2638_ = lean_ctor_get(v_tree_2595_, 4);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v_tree_2595_, 3);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_tree_2595_, 2);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_tree_2595_, 1);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v_tree_2595_, 0);
lean_dec(v_unused_2642_);
v___x_2632_ = v_tree_2595_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_dec(v_tree_2595_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 4, v___x_2630_);
lean_ctor_set(v___x_2632_, 3, v___y_2625_);
lean_ctor_set(v___x_2632_, 2, v_v_2613_);
lean_ctor_set(v___x_2632_, 1, v_k_2612_);
lean_ctor_set(v___x_2632_, 0, v___x_2623_);
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_k_2612_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_v_2613_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v___y_2625_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v___x_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
v___jp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = lean_nat_add(v___x_2644_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec(v___x_2644_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_l_2614_);
lean_ctor_set(v___x_2592_, 3, v_l_2441_);
lean_ctor_set(v___x_2592_, 2, v_v_2440_);
lean_ctor_set(v___x_2592_, 1, v_k_2439_);
lean_ctor_set(v___x_2592_, 0, v___x_2647_);
v___x_2649_ = v___x_2592_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_l_2441_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v_l_2614_);
v___x_2649_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_nat_add(v___x_2448_, v_size_2598_);
if (lean_obj_tag(v_r_2615_) == 0)
{
lean_object* v_size_2651_; 
v_size_2651_ = lean_ctor_get(v_r_2615_, 0);
lean_inc(v_size_2651_);
v___y_2625_ = v___x_2649_;
v___y_2626_ = v___x_2650_;
v___y_2627_ = v_size_2651_;
goto v___jp_2624_;
}
else
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_unsigned_to_nat(0u);
v___y_2625_ = v___x_2649_;
v___y_2626_ = v___x_2650_;
v___y_2627_ = v___x_2652_;
goto v___jp_2624_;
}
}
}
}
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2662_ = lean_nat_add(v___x_2448_, v_size_2438_);
lean_dec(v_size_2438_);
v___x_2663_ = lean_nat_add(v___x_2662_, v_size_2598_);
lean_dec(v___x_2662_);
v___x_2664_ = lean_nat_add(v___x_2448_, v_size_2598_);
v___x_2665_ = lean_nat_add(v___x_2664_, v_size_2611_);
lean_dec(v___x_2664_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_tree_2595_);
lean_ctor_set(v___x_2592_, 3, v_r_2442_);
lean_ctor_set(v___x_2592_, 2, v_v_2597_);
lean_ctor_set(v___x_2592_, 1, v_k_2596_);
lean_ctor_set(v___x_2592_, 0, v___x_2665_);
v___x_2667_ = v___x_2592_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_k_2596_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_v_2597_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_r_2442_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_tree_2595_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 4, v___x_2667_);
lean_ctor_set(v___x_2608_, 0, v___x_2663_);
v___x_2669_ = v___x_2608_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_l_2441_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2441_) == 0)
{
lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2701_; 
lean_inc_ref(v_l_2441_);
lean_inc(v_v_2440_);
lean_inc(v_k_2439_);
lean_inc(v_size_2438_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2702_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_l_2258_, 2);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_l_2258_, 1);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_l_2258_, 0);
lean_dec(v_unused_2706_);
v___x_2679_ = v_l_2258_;
v_isShared_2680_ = v_isSharedCheck_2701_;
goto v_resetjp_2678_;
}
else
{
lean_dec(v_l_2258_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2701_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
if (lean_obj_tag(v_r_2442_) == 0)
{
lean_object* v_k_2681_; lean_object* v_v_2682_; lean_object* v_size_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v_k_2681_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_k_2681_);
v_v_2682_ = lean_ctor_get(v___x_2594_, 1);
lean_inc(v_v_2682_);
lean_dec_ref(v___x_2594_);
v_size_2683_ = lean_ctor_get(v_r_2442_, 0);
v___x_2684_ = lean_nat_add(v___x_2448_, v_size_2438_);
lean_dec(v_size_2438_);
v___x_2685_ = lean_nat_add(v___x_2448_, v_size_2683_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_tree_2595_);
lean_ctor_set(v___x_2592_, 3, v_r_2442_);
lean_ctor_set(v___x_2592_, 2, v_v_2682_);
lean_ctor_set(v___x_2592_, 1, v_k_2681_);
lean_ctor_set(v___x_2592_, 0, v___x_2685_);
v___x_2687_ = v___x_2592_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_k_2681_);
lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_v_2682_);
lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_r_2442_);
lean_ctor_set(v_reuseFailAlloc_2691_, 4, v_tree_2595_);
v___x_2687_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2689_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 4, v___x_2687_);
lean_ctor_set(v___x_2679_, 0, v___x_2684_);
v___x_2689_ = v___x_2679_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_l_2441_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_object* v_k_2692_; lean_object* v_v_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
lean_dec(v_size_2438_);
v_k_2692_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_k_2692_);
v_v_2693_ = lean_ctor_get(v___x_2594_, 1);
lean_inc(v_v_2693_);
lean_dec_ref(v___x_2594_);
v___x_2694_ = lean_unsigned_to_nat(3u);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_r_2442_);
lean_ctor_set(v___x_2592_, 3, v_r_2442_);
lean_ctor_set(v___x_2592_, 2, v_v_2693_);
lean_ctor_set(v___x_2592_, 1, v_k_2692_);
lean_ctor_set(v___x_2592_, 0, v___x_2448_);
v___x_2696_ = v___x_2592_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_k_2692_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_v_2693_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_r_2442_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_r_2442_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 4, v___x_2696_);
lean_ctor_set(v___x_2679_, 0, v___x_2694_);
v___x_2698_ = v___x_2679_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_l_2441_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2442_) == 0)
{
lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2731_; 
lean_inc(v_l_2441_);
lean_inc(v_v_2440_);
lean_inc(v_k_2439_);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2732_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2732_);
v_unused_2733_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_l_2258_, 2);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_l_2258_, 1);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_l_2258_, 0);
lean_dec(v_unused_2736_);
v___x_2708_ = v_l_2258_;
v_isShared_2709_ = v_isSharedCheck_2731_;
goto v_resetjp_2707_;
}
else
{
lean_dec(v_l_2258_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2731_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_k_2710_; lean_object* v_v_2711_; lean_object* v_k_2712_; lean_object* v_v_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2727_; 
v_k_2710_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_k_2710_);
v_v_2711_ = lean_ctor_get(v___x_2594_, 1);
lean_inc(v_v_2711_);
lean_dec_ref(v___x_2594_);
v_k_2712_ = lean_ctor_get(v_r_2442_, 1);
v_v_2713_ = lean_ctor_get(v_r_2442_, 2);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_r_2442_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; 
v_unused_2728_ = lean_ctor_get(v_r_2442_, 4);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_r_2442_, 3);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_r_2442_, 0);
lean_dec(v_unused_2730_);
v___x_2715_ = v_r_2442_;
v_isShared_2716_ = v_isSharedCheck_2727_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_v_2713_);
lean_inc(v_k_2712_);
lean_dec(v_r_2442_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2727_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = lean_unsigned_to_nat(3u);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 4, v_l_2441_);
lean_ctor_set(v___x_2715_, 3, v_l_2441_);
lean_ctor_set(v___x_2715_, 2, v_v_2440_);
lean_ctor_set(v___x_2715_, 1, v_k_2439_);
lean_ctor_set(v___x_2715_, 0, v___x_2448_);
v___x_2719_ = v___x_2715_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_l_2441_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_l_2441_);
v___x_2719_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2721_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_l_2441_);
lean_ctor_set(v___x_2592_, 3, v_l_2441_);
lean_ctor_set(v___x_2592_, 2, v_v_2711_);
lean_ctor_set(v___x_2592_, 1, v_k_2710_);
lean_ctor_set(v___x_2592_, 0, v___x_2448_);
v___x_2721_ = v___x_2592_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_k_2710_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_v_2711_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_l_2441_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_l_2441_);
v___x_2721_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2723_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 4, v___x_2721_);
lean_ctor_set(v___x_2708_, 3, v___x_2719_);
lean_ctor_set(v___x_2708_, 2, v_v_2713_);
lean_ctor_set(v___x_2708_, 1, v_k_2712_);
lean_ctor_set(v___x_2708_, 0, v___x_2717_);
v___x_2723_ = v___x_2708_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_k_2712_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_v_2713_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
else
{
lean_object* v_k_2737_; lean_object* v_v_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v_k_2737_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_k_2737_);
v_v_2738_ = lean_ctor_get(v___x_2594_, 1);
lean_inc(v_v_2738_);
lean_dec_ref(v___x_2594_);
v___x_2739_ = lean_unsigned_to_nat(2u);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_r_2442_);
lean_ctor_set(v___x_2592_, 3, v_l_2258_);
lean_ctor_set(v___x_2592_, 2, v_v_2738_);
lean_ctor_set(v___x_2592_, 1, v_k_2737_);
lean_ctor_set(v___x_2592_, 0, v___x_2739_);
v___x_2741_ = v___x_2592_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_k_2737_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_v_2738_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_r_2442_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
}
}
else
{
return v_l_2258_;
}
}
else
{
return v_r_2259_;
}
}
default: 
{
lean_object* v_impl_2749_; lean_object* v___x_2750_; 
v_impl_2749_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2254_, v_r_2259_);
v___x_2750_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2749_) == 0)
{
if (lean_obj_tag(v_l_2258_) == 0)
{
lean_object* v_size_2751_; lean_object* v_size_2752_; lean_object* v_k_2753_; lean_object* v_v_2754_; lean_object* v_l_2755_; lean_object* v_r_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_size_2751_ = lean_ctor_get(v_impl_2749_, 0);
v_size_2752_ = lean_ctor_get(v_l_2258_, 0);
v_k_2753_ = lean_ctor_get(v_l_2258_, 1);
v_v_2754_ = lean_ctor_get(v_l_2258_, 2);
v_l_2755_ = lean_ctor_get(v_l_2258_, 3);
v_r_2756_ = lean_ctor_get(v_l_2258_, 4);
lean_inc(v_r_2756_);
v___x_2757_ = lean_unsigned_to_nat(3u);
v___x_2758_ = lean_nat_mul(v___x_2757_, v_size_2751_);
v___x_2759_ = lean_nat_dec_lt(v___x_2758_, v_size_2752_);
lean_dec(v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
lean_dec(v_r_2756_);
v___x_2760_ = lean_nat_add(v___x_2750_, v_size_2752_);
v___x_2761_ = lean_nat_add(v___x_2760_, v_size_2751_);
lean_dec(v___x_2760_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_impl_2749_);
lean_ctor_set(v___x_2261_, 0, v___x_2761_);
v___x_2763_ = v___x_2261_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2764_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2764_, 4, v_impl_2749_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
else
{
lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2830_; 
lean_inc(v_l_2755_);
lean_inc(v_v_2754_);
lean_inc(v_k_2753_);
lean_inc(v_size_2752_);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; lean_object* v_unused_2832_; lean_object* v_unused_2833_; lean_object* v_unused_2834_; lean_object* v_unused_2835_; 
v_unused_2831_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2832_);
v_unused_2833_ = lean_ctor_get(v_l_2258_, 2);
lean_dec(v_unused_2833_);
v_unused_2834_ = lean_ctor_get(v_l_2258_, 1);
lean_dec(v_unused_2834_);
v_unused_2835_ = lean_ctor_get(v_l_2258_, 0);
lean_dec(v_unused_2835_);
v___x_2766_ = v_l_2258_;
v_isShared_2767_ = v_isSharedCheck_2830_;
goto v_resetjp_2765_;
}
else
{
lean_dec(v_l_2258_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2830_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_size_2768_; lean_object* v_size_2769_; lean_object* v_k_2770_; lean_object* v_v_2771_; lean_object* v_l_2772_; lean_object* v_r_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v_size_2768_ = lean_ctor_get(v_l_2755_, 0);
v_size_2769_ = lean_ctor_get(v_r_2756_, 0);
v_k_2770_ = lean_ctor_get(v_r_2756_, 1);
v_v_2771_ = lean_ctor_get(v_r_2756_, 2);
v_l_2772_ = lean_ctor_get(v_r_2756_, 3);
v_r_2773_ = lean_ctor_get(v_r_2756_, 4);
v___x_2774_ = lean_unsigned_to_nat(2u);
v___x_2775_ = lean_nat_mul(v___x_2774_, v_size_2768_);
v___x_2776_ = lean_nat_dec_lt(v_size_2769_, v___x_2775_);
lean_dec(v___x_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2805_; 
lean_inc(v_r_2773_);
lean_inc(v_l_2772_);
lean_inc(v_v_2771_);
lean_inc(v_k_2770_);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_r_2756_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; 
v_unused_2806_ = lean_ctor_get(v_r_2756_, 4);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_r_2756_, 3);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_r_2756_, 2);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_r_2756_, 1);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_r_2756_, 0);
lean_dec(v_unused_2810_);
v___x_2778_ = v_r_2756_;
v_isShared_2779_ = v_isSharedCheck_2805_;
goto v_resetjp_2777_;
}
else
{
lean_dec(v_r_2756_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2805_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___x_2793_; lean_object* v___y_2795_; 
v___x_2780_ = lean_nat_add(v___x_2750_, v_size_2752_);
lean_dec(v_size_2752_);
v___x_2781_ = lean_nat_add(v___x_2780_, v_size_2751_);
lean_dec(v___x_2780_);
v___x_2793_ = lean_nat_add(v___x_2750_, v_size_2768_);
if (lean_obj_tag(v_l_2772_) == 0)
{
lean_object* v_size_2803_; 
v_size_2803_ = lean_ctor_get(v_l_2772_, 0);
lean_inc(v_size_2803_);
v___y_2795_ = v_size_2803_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_unsigned_to_nat(0u);
v___y_2795_ = v___x_2804_;
goto v___jp_2794_;
}
v___jp_2782_:
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2786_ = lean_nat_add(v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec(v___y_2784_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 4, v_impl_2749_);
lean_ctor_set(v___x_2778_, 3, v_r_2773_);
lean_ctor_set(v___x_2778_, 2, v_v_2257_);
lean_ctor_set(v___x_2778_, 1, v_k_2256_);
lean_ctor_set(v___x_2778_, 0, v___x_2786_);
v___x_2788_ = v___x_2778_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v_r_2773_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v_impl_2749_);
v___x_2788_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2790_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v___x_2788_);
lean_ctor_set(v___x_2766_, 3, v___y_2783_);
lean_ctor_set(v___x_2766_, 2, v_v_2771_);
lean_ctor_set(v___x_2766_, 1, v_k_2770_);
lean_ctor_set(v___x_2766_, 0, v___x_2781_);
v___x_2790_ = v___x_2766_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_k_2770_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_v_2771_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v___y_2783_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
v___jp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = lean_nat_add(v___x_2793_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec(v___x_2793_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_l_2772_);
lean_ctor_set(v___x_2261_, 3, v_l_2755_);
lean_ctor_set(v___x_2261_, 2, v_v_2754_);
lean_ctor_set(v___x_2261_, 1, v_k_2753_);
lean_ctor_set(v___x_2261_, 0, v___x_2796_);
v___x_2798_ = v___x_2261_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_k_2753_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v_v_2754_);
lean_ctor_set(v_reuseFailAlloc_2802_, 3, v_l_2755_);
lean_ctor_set(v_reuseFailAlloc_2802_, 4, v_l_2772_);
v___x_2798_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_nat_add(v___x_2750_, v_size_2751_);
if (lean_obj_tag(v_r_2773_) == 0)
{
lean_object* v_size_2800_; 
v_size_2800_ = lean_ctor_get(v_r_2773_, 0);
lean_inc(v_size_2800_);
v___y_2783_ = v___x_2798_;
v___y_2784_ = v___x_2799_;
v___y_2785_ = v_size_2800_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___y_2783_ = v___x_2798_;
v___y_2784_ = v___x_2799_;
v___y_2785_ = v___x_2801_;
goto v___jp_2782_;
}
}
}
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
lean_del_object(v___x_2261_);
v___x_2811_ = lean_nat_add(v___x_2750_, v_size_2752_);
lean_dec(v_size_2752_);
v___x_2812_ = lean_nat_add(v___x_2811_, v_size_2751_);
lean_dec(v___x_2811_);
v___x_2813_ = lean_nat_add(v___x_2750_, v_size_2751_);
v___x_2814_ = lean_nat_add(v___x_2813_, v_size_2769_);
lean_dec(v___x_2813_);
lean_inc_ref(v_impl_2749_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v_impl_2749_);
lean_ctor_set(v___x_2766_, 3, v_r_2756_);
lean_ctor_set(v___x_2766_, 2, v_v_2257_);
lean_ctor_set(v___x_2766_, 1, v_k_2256_);
lean_ctor_set(v___x_2766_, 0, v___x_2814_);
v___x_2816_ = v___x_2766_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2814_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_r_2756_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_impl_2749_);
v___x_2816_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_isSharedCheck_2823_ = !lean_is_exclusive(v_impl_2749_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; lean_object* v_unused_2825_; lean_object* v_unused_2826_; lean_object* v_unused_2827_; lean_object* v_unused_2828_; 
v_unused_2824_ = lean_ctor_get(v_impl_2749_, 4);
lean_dec(v_unused_2824_);
v_unused_2825_ = lean_ctor_get(v_impl_2749_, 3);
lean_dec(v_unused_2825_);
v_unused_2826_ = lean_ctor_get(v_impl_2749_, 2);
lean_dec(v_unused_2826_);
v_unused_2827_ = lean_ctor_get(v_impl_2749_, 1);
lean_dec(v_unused_2827_);
v_unused_2828_ = lean_ctor_get(v_impl_2749_, 0);
lean_dec(v_unused_2828_);
v___x_2818_ = v_impl_2749_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v_impl_2749_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 4, v___x_2816_);
lean_ctor_set(v___x_2818_, 3, v_l_2755_);
lean_ctor_set(v___x_2818_, 2, v_v_2754_);
lean_ctor_set(v___x_2818_, 1, v_k_2753_);
lean_ctor_set(v___x_2818_, 0, v___x_2812_);
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_k_2753_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_v_2754_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_l_2755_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v___x_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v_size_2836_ = lean_ctor_get(v_impl_2749_, 0);
v___x_2837_ = lean_nat_add(v___x_2750_, v_size_2836_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_impl_2749_);
lean_ctor_set(v___x_2261_, 0, v___x_2837_);
v___x_2839_ = v___x_2261_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_impl_2749_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
else
{
if (lean_obj_tag(v_l_2258_) == 0)
{
lean_object* v_l_2841_; 
v_l_2841_ = lean_ctor_get(v_l_2258_, 3);
if (lean_obj_tag(v_l_2841_) == 0)
{
lean_object* v_r_2842_; 
lean_inc_ref(v_l_2841_);
v_r_2842_ = lean_ctor_get(v_l_2258_, 4);
lean_inc(v_r_2842_);
if (lean_obj_tag(v_r_2842_) == 0)
{
lean_object* v_size_2843_; lean_object* v_k_2844_; lean_object* v_v_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2858_; 
v_size_2843_ = lean_ctor_get(v_l_2258_, 0);
v_k_2844_ = lean_ctor_get(v_l_2258_, 1);
v_v_2845_ = lean_ctor_get(v_l_2258_, 2);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; lean_object* v_unused_2860_; 
v_unused_2859_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2859_);
v_unused_2860_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2860_);
v___x_2847_ = v_l_2258_;
v_isShared_2848_ = v_isSharedCheck_2858_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_v_2845_);
lean_inc(v_k_2844_);
lean_inc(v_size_2843_);
lean_dec(v_l_2258_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2858_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v_size_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
v_size_2849_ = lean_ctor_get(v_r_2842_, 0);
v___x_2850_ = lean_nat_add(v___x_2750_, v_size_2843_);
lean_dec(v_size_2843_);
v___x_2851_ = lean_nat_add(v___x_2750_, v_size_2849_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 4, v_impl_2749_);
lean_ctor_set(v___x_2847_, 3, v_r_2842_);
lean_ctor_set(v___x_2847_, 2, v_v_2257_);
lean_ctor_set(v___x_2847_, 1, v_k_2256_);
lean_ctor_set(v___x_2847_, 0, v___x_2851_);
v___x_2853_ = v___x_2847_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_r_2842_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_impl_2749_);
v___x_2853_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2855_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v___x_2853_);
lean_ctor_set(v___x_2261_, 3, v_l_2841_);
lean_ctor_set(v___x_2261_, 2, v_v_2845_);
lean_ctor_set(v___x_2261_, 1, v_k_2844_);
lean_ctor_set(v___x_2261_, 0, v___x_2850_);
v___x_2855_ = v___x_2261_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_k_2844_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_v_2845_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_l_2841_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_k_2861_; lean_object* v_v_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2873_; 
v_k_2861_ = lean_ctor_get(v_l_2258_, 1);
v_v_2862_ = lean_ctor_get(v_l_2258_, 2);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; lean_object* v_unused_2875_; lean_object* v_unused_2876_; 
v_unused_2874_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2874_);
v_unused_2875_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2875_);
v_unused_2876_ = lean_ctor_get(v_l_2258_, 0);
lean_dec(v_unused_2876_);
v___x_2864_ = v_l_2258_;
v_isShared_2865_ = v_isSharedCheck_2873_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_v_2862_);
lean_inc(v_k_2861_);
lean_dec(v_l_2258_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2873_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2866_ = lean_unsigned_to_nat(3u);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 3, v_r_2842_);
lean_ctor_set(v___x_2864_, 2, v_v_2257_);
lean_ctor_set(v___x_2864_, 1, v_k_2256_);
lean_ctor_set(v___x_2864_, 0, v___x_2750_);
v___x_2868_ = v___x_2864_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_r_2842_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_r_2842_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v___x_2868_);
lean_ctor_set(v___x_2261_, 3, v_l_2841_);
lean_ctor_set(v___x_2261_, 2, v_v_2862_);
lean_ctor_set(v___x_2261_, 1, v_k_2861_);
lean_ctor_set(v___x_2261_, 0, v___x_2866_);
v___x_2870_ = v___x_2261_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_k_2861_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_v_2862_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_l_2841_);
lean_ctor_set(v_reuseFailAlloc_2871_, 4, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
else
{
lean_object* v_r_2877_; 
v_r_2877_ = lean_ctor_get(v_l_2258_, 4);
lean_inc(v_r_2877_);
if (lean_obj_tag(v_r_2877_) == 0)
{
lean_object* v_k_2878_; lean_object* v_v_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2902_; 
lean_inc(v_l_2841_);
v_k_2878_ = lean_ctor_get(v_l_2258_, 1);
v_v_2879_ = lean_ctor_get(v_l_2258_, 2);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_l_2258_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; lean_object* v_unused_2904_; lean_object* v_unused_2905_; 
v_unused_2903_ = lean_ctor_get(v_l_2258_, 4);
lean_dec(v_unused_2903_);
v_unused_2904_ = lean_ctor_get(v_l_2258_, 3);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v_l_2258_, 0);
lean_dec(v_unused_2905_);
v___x_2881_ = v_l_2258_;
v_isShared_2882_ = v_isSharedCheck_2902_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_v_2879_);
lean_inc(v_k_2878_);
lean_dec(v_l_2258_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2902_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_k_2883_; lean_object* v_v_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2898_; 
v_k_2883_ = lean_ctor_get(v_r_2877_, 1);
v_v_2884_ = lean_ctor_get(v_r_2877_, 2);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_r_2877_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; lean_object* v_unused_2900_; lean_object* v_unused_2901_; 
v_unused_2899_ = lean_ctor_get(v_r_2877_, 4);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_r_2877_, 3);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_r_2877_, 0);
lean_dec(v_unused_2901_);
v___x_2886_ = v_r_2877_;
v_isShared_2887_ = v_isSharedCheck_2898_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_v_2884_);
lean_inc(v_k_2883_);
lean_dec(v_r_2877_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2898_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = lean_unsigned_to_nat(3u);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 4, v_l_2841_);
lean_ctor_set(v___x_2886_, 3, v_l_2841_);
lean_ctor_set(v___x_2886_, 2, v_v_2879_);
lean_ctor_set(v___x_2886_, 1, v_k_2878_);
lean_ctor_set(v___x_2886_, 0, v___x_2750_);
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_k_2878_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_v_2879_);
lean_ctor_set(v_reuseFailAlloc_2897_, 3, v_l_2841_);
lean_ctor_set(v_reuseFailAlloc_2897_, 4, v_l_2841_);
v___x_2890_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2892_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 4, v_l_2841_);
lean_ctor_set(v___x_2881_, 2, v_v_2257_);
lean_ctor_set(v___x_2881_, 1, v_k_2256_);
lean_ctor_set(v___x_2881_, 0, v___x_2750_);
v___x_2892_ = v___x_2881_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_l_2841_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_l_2841_);
v___x_2892_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2894_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v___x_2892_);
lean_ctor_set(v___x_2261_, 3, v___x_2890_);
lean_ctor_set(v___x_2261_, 2, v_v_2884_);
lean_ctor_set(v___x_2261_, 1, v_k_2883_);
lean_ctor_set(v___x_2261_, 0, v___x_2888_);
v___x_2894_ = v___x_2261_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_k_2883_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_v_2884_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v___x_2892_);
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
else
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = lean_unsigned_to_nat(2u);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_r_2877_);
lean_ctor_set(v___x_2261_, 0, v___x_2906_);
v___x_2908_ = v___x_2261_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_r_2877_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_object* v___x_2911_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_l_2258_);
lean_ctor_set(v___x_2261_, 0, v___x_2750_);
v___x_2911_ = v___x_2261_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_l_2258_);
lean_ctor_set(v_reuseFailAlloc_2912_, 4, v_l_2258_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
}
else
{
return v_t_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_2915_, lean_object* v_t_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2915_, v_t_2916_);
lean_dec(v_k_2915_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_2918_, lean_object* v_declName_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v_ext_2925_; lean_object* v_toEnvExtension_2926_; lean_object* v_env_2927_; lean_object* v_asyncMode_2928_; uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v_funCC_2931_; lean_object* v___y_2933_; uint8_t v___x_2959_; 
v___x_2923_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2924_ = lean_st_ref_get(v_a_2921_);
v_ext_2925_ = lean_ctor_get(v_ext_2918_, 1);
v_toEnvExtension_2926_ = lean_ctor_get(v_ext_2925_, 0);
v_env_2927_ = lean_ctor_get(v___x_2924_, 0);
lean_inc_ref(v_env_2927_);
lean_dec(v___x_2924_);
v_asyncMode_2928_ = lean_ctor_get(v_toEnvExtension_2926_, 2);
v___x_2929_ = 0;
v___x_2930_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2923_, v_ext_2918_, v_env_2927_, v_asyncMode_2928_, v___x_2929_);
v_funCC_2931_ = lean_ctor_get(v___x_2930_, 2);
lean_inc(v_funCC_2931_);
lean_dec(v___x_2930_);
v___x_2959_ = l_Lean_NameSet_contains(v_funCC_2931_, v_declName_2919_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; 
lean_inc(v_declName_2919_);
v___x_2960_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2919_, v_a_2920_, v_a_2921_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_dec_ref_known(v___x_2960_, 1);
v___y_2933_ = v_a_2921_;
goto v___jp_2932_;
}
else
{
lean_dec(v_funCC_2931_);
lean_dec(v_declName_2919_);
lean_dec_ref(v_ext_2918_);
return v___x_2960_;
}
}
else
{
v___y_2933_ = v_a_2921_;
goto v___jp_2932_;
}
v___jp_2932_:
{
lean_object* v___x_2934_; lean_object* v___f_2935_; lean_object* v___x_2936_; lean_object* v_env_2937_; lean_object* v_nextMacroScope_2938_; lean_object* v_ngen_2939_; lean_object* v_auxDeclNGen_2940_; lean_object* v_traceState_2941_; lean_object* v_recordedDeps_2942_; lean_object* v_messages_2943_; lean_object* v_infoState_2944_; lean_object* v_snapshotTasks_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2957_; 
v___x_2934_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_2919_, v_funCC_2931_);
lean_dec(v_declName_2919_);
v___f_2935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_2935_, 0, v___x_2934_);
v___x_2936_ = lean_st_ref_take(v___y_2933_);
v_env_2937_ = lean_ctor_get(v___x_2936_, 0);
v_nextMacroScope_2938_ = lean_ctor_get(v___x_2936_, 1);
v_ngen_2939_ = lean_ctor_get(v___x_2936_, 2);
v_auxDeclNGen_2940_ = lean_ctor_get(v___x_2936_, 3);
v_traceState_2941_ = lean_ctor_get(v___x_2936_, 4);
v_recordedDeps_2942_ = lean_ctor_get(v___x_2936_, 6);
v_messages_2943_ = lean_ctor_get(v___x_2936_, 7);
v_infoState_2944_ = lean_ctor_get(v___x_2936_, 8);
v_snapshotTasks_2945_ = lean_ctor_get(v___x_2936_, 9);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v___x_2936_, 5);
lean_dec(v_unused_2958_);
v___x_2947_ = v___x_2936_;
v_isShared_2948_ = v_isSharedCheck_2957_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_snapshotTasks_2945_);
lean_inc(v_infoState_2944_);
lean_inc(v_messages_2943_);
lean_inc(v_recordedDeps_2942_);
lean_inc(v_traceState_2941_);
lean_inc(v_auxDeclNGen_2940_);
lean_inc(v_ngen_2939_);
lean_inc(v_nextMacroScope_2938_);
lean_inc(v_env_2937_);
lean_dec(v___x_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2957_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2949_ = lean_box(0);
v___x_2950_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2918_, v_env_2937_, v___f_2935_);
v___x_2951_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 5, v___x_2951_);
lean_ctor_set(v___x_2947_, 0, v___x_2950_);
v___x_2953_ = v___x_2947_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_nextMacroScope_2938_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_ngen_2939_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_auxDeclNGen_2940_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_traceState_2941_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_recordedDeps_2942_);
lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_messages_2943_);
lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_infoState_2944_);
lean_ctor_set(v_reuseFailAlloc_2956_, 9, v_snapshotTasks_2945_);
v___x_2953_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_st_ref_put(v___y_2933_, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2949_);
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_2961_, lean_object* v_declName_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2961_, v_declName_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_2967_, lean_object* v_k_2968_, lean_object* v_t_2969_, lean_object* v_h_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_2968_, v_t_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_2972_, lean_object* v_k_2973_, lean_object* v_t_2974_, lean_object* v_h_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_2972_, v_k_2973_, v_t_2974_, v_h_2975_);
lean_dec(v_k_2973_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_2977_, lean_object* v_s_2978_){
_start:
{
lean_object* v_casesTypes_2979_; lean_object* v_extThms_2980_; lean_object* v_funCC_2981_; lean_object* v_inj_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_casesTypes_2979_ = lean_ctor_get(v_s_2978_, 0);
v_extThms_2980_ = lean_ctor_get(v_s_2978_, 1);
v_funCC_2981_ = lean_ctor_get(v_s_2978_, 2);
v_inj_2982_ = lean_ctor_get(v_s_2978_, 4);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_s_2978_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_s_2978_, 3);
lean_dec(v_unused_2990_);
v___x_2984_ = v_s_2978_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_inj_2982_);
lean_inc(v_funCC_2981_);
lean_inc(v_extThms_2980_);
lean_inc(v_casesTypes_2979_);
lean_dec(v_s_2978_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 3, v_a_2977_);
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_casesTypes_2979_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_extThms_2980_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_funCC_2981_);
lean_ctor_set(v_reuseFailAlloc_2988_, 3, v_a_2977_);
lean_ctor_set(v_reuseFailAlloc_2988_, 4, v_inj_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_2991_, lean_object* v_declName_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_ext_3000_; lean_object* v_toEnvExtension_3001_; lean_object* v_env_3002_; lean_object* v_asyncMode_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v_ematch_3006_; lean_object* v___x_3007_; 
v___x_2998_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2999_ = lean_st_ref_get(v_a_2996_);
v_ext_3000_ = lean_ctor_get(v_ext_2991_, 1);
v_toEnvExtension_3001_ = lean_ctor_get(v_ext_3000_, 0);
v_env_3002_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_env_3002_);
lean_dec(v___x_2999_);
v_asyncMode_3003_ = lean_ctor_get(v_toEnvExtension_3001_, 2);
v___x_3004_ = 0;
v___x_3005_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2998_, v_ext_2991_, v_env_3002_, v_asyncMode_3003_, v___x_3004_);
v_ematch_3006_ = lean_ctor_get(v___x_3005_, 3);
lean_inc_ref(v_ematch_3006_);
lean_dec(v___x_3005_);
v___x_3007_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_3006_, v_declName_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3053_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3053_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3053_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___f_3012_; lean_object* v___x_3013_; lean_object* v_env_3014_; lean_object* v_nextMacroScope_3015_; lean_object* v_ngen_3016_; lean_object* v_auxDeclNGen_3017_; lean_object* v_traceState_3018_; lean_object* v_recordedDeps_3019_; lean_object* v_messages_3020_; lean_object* v_infoState_3021_; lean_object* v_snapshotTasks_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3051_; 
v___f_3012_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_3012_, 0, v_a_3008_);
v___x_3013_ = lean_st_ref_take(v_a_2996_);
v_env_3014_ = lean_ctor_get(v___x_3013_, 0);
v_nextMacroScope_3015_ = lean_ctor_get(v___x_3013_, 1);
v_ngen_3016_ = lean_ctor_get(v___x_3013_, 2);
v_auxDeclNGen_3017_ = lean_ctor_get(v___x_3013_, 3);
v_traceState_3018_ = lean_ctor_get(v___x_3013_, 4);
v_recordedDeps_3019_ = lean_ctor_get(v___x_3013_, 6);
v_messages_3020_ = lean_ctor_get(v___x_3013_, 7);
v_infoState_3021_ = lean_ctor_get(v___x_3013_, 8);
v_snapshotTasks_3022_ = lean_ctor_get(v___x_3013_, 9);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3013_, 5);
lean_dec(v_unused_3052_);
v___x_3024_ = v___x_3013_;
v_isShared_3025_ = v_isSharedCheck_3051_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_snapshotTasks_3022_);
lean_inc(v_infoState_3021_);
lean_inc(v_messages_3020_);
lean_inc(v_recordedDeps_3019_);
lean_inc(v_traceState_3018_);
lean_inc(v_auxDeclNGen_3017_);
lean_inc(v_ngen_3016_);
lean_inc(v_nextMacroScope_3015_);
lean_inc(v_env_3014_);
lean_dec(v___x_3013_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3051_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3026_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_2991_, v_env_3014_, v___f_3012_);
v___x_3027_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 5, v___x_3027_);
lean_ctor_set(v___x_3024_, 0, v___x_3026_);
v___x_3029_ = v___x_3024_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_nextMacroScope_3015_);
lean_ctor_set(v_reuseFailAlloc_3050_, 2, v_ngen_3016_);
lean_ctor_set(v_reuseFailAlloc_3050_, 3, v_auxDeclNGen_3017_);
lean_ctor_set(v_reuseFailAlloc_3050_, 4, v_traceState_3018_);
lean_ctor_set(v_reuseFailAlloc_3050_, 5, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3050_, 6, v_recordedDeps_3019_);
lean_ctor_set(v_reuseFailAlloc_3050_, 7, v_messages_3020_);
lean_ctor_set(v_reuseFailAlloc_3050_, 8, v_infoState_3021_);
lean_ctor_set(v_reuseFailAlloc_3050_, 9, v_snapshotTasks_3022_);
v___x_3029_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v_mctx_3032_; lean_object* v_zetaDeltaFVarIds_3033_; lean_object* v_postponed_3034_; lean_object* v_diag_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3048_; 
v___x_3030_ = lean_st_ref_put(v_a_2996_, v___x_3029_);
v___x_3031_ = lean_st_ref_take(v_a_2994_);
v_mctx_3032_ = lean_ctor_get(v___x_3031_, 0);
v_zetaDeltaFVarIds_3033_ = lean_ctor_get(v___x_3031_, 2);
v_postponed_3034_ = lean_ctor_get(v___x_3031_, 3);
v_diag_3035_ = lean_ctor_get(v___x_3031_, 4);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v___x_3031_, 1);
lean_dec(v_unused_3049_);
v___x_3037_ = v___x_3031_;
v_isShared_3038_ = v_isSharedCheck_3048_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_diag_3035_);
lean_inc(v_postponed_3034_);
lean_inc(v_zetaDeltaFVarIds_3033_);
lean_inc(v_mctx_3032_);
lean_dec(v___x_3031_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3048_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3040_);
v___x_3042_ = v___x_3037_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_mctx_3032_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_zetaDeltaFVarIds_3033_);
lean_ctor_set(v_reuseFailAlloc_3047_, 3, v_postponed_3034_);
lean_ctor_set(v_reuseFailAlloc_3047_, 4, v_diag_3035_);
v___x_3042_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3043_ = lean_st_ref_put(v_a_2994_, v___x_3042_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3039_);
v___x_3045_ = v___x_3010_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3039_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v_ext_2991_);
v_a_3054_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3007_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3007_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_3062_, lean_object* v_declName_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3062_, v_declName_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_3070_, lean_object* v_s_3071_){
_start:
{
lean_object* v_casesTypes_3072_; lean_object* v_extThms_3073_; lean_object* v_funCC_3074_; lean_object* v_ematch_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
v_casesTypes_3072_ = lean_ctor_get(v_s_3071_, 0);
v_extThms_3073_ = lean_ctor_get(v_s_3071_, 1);
v_funCC_3074_ = lean_ctor_get(v_s_3071_, 2);
v_ematch_3075_ = lean_ctor_get(v_s_3071_, 3);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_s_3071_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v_s_3071_, 4);
lean_dec(v_unused_3083_);
v___x_3077_ = v_s_3071_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_ematch_3075_);
lean_inc(v_funCC_3074_);
lean_inc(v_extThms_3073_);
lean_inc(v_casesTypes_3072_);
lean_dec(v_s_3071_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 4, v_a_3070_);
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_casesTypes_3072_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_extThms_3073_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_funCC_3074_);
lean_ctor_set(v_reuseFailAlloc_3081_, 3, v_ematch_3075_);
lean_ctor_set(v_reuseFailAlloc_3081_, 4, v_a_3070_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_3084_, lean_object* v_declName_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v_ext_3093_; lean_object* v_toEnvExtension_3094_; lean_object* v_env_3095_; lean_object* v_asyncMode_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v_inj_3099_; lean_object* v___x_3100_; 
v___x_3091_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3092_ = lean_st_ref_get(v_a_3089_);
v_ext_3093_ = lean_ctor_get(v_ext_3084_, 1);
v_toEnvExtension_3094_ = lean_ctor_get(v_ext_3093_, 0);
v_env_3095_ = lean_ctor_get(v___x_3092_, 0);
lean_inc_ref(v_env_3095_);
lean_dec(v___x_3092_);
v_asyncMode_3096_ = lean_ctor_get(v_toEnvExtension_3094_, 2);
v___x_3097_ = 0;
v___x_3098_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3091_, v_ext_3084_, v_env_3095_, v_asyncMode_3096_, v___x_3097_);
v_inj_3099_ = lean_ctor_get(v___x_3098_, 4);
lean_inc_ref(v_inj_3099_);
lean_dec(v___x_3098_);
v___x_3100_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_3099_, v_declName_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3146_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3146_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3146_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v_env_3107_; lean_object* v_nextMacroScope_3108_; lean_object* v_ngen_3109_; lean_object* v_auxDeclNGen_3110_; lean_object* v_traceState_3111_; lean_object* v_recordedDeps_3112_; lean_object* v_messages_3113_; lean_object* v_infoState_3114_; lean_object* v_snapshotTasks_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3144_; 
v___f_3105_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_3105_, 0, v_a_3101_);
v___x_3106_ = lean_st_ref_take(v_a_3089_);
v_env_3107_ = lean_ctor_get(v___x_3106_, 0);
v_nextMacroScope_3108_ = lean_ctor_get(v___x_3106_, 1);
v_ngen_3109_ = lean_ctor_get(v___x_3106_, 2);
v_auxDeclNGen_3110_ = lean_ctor_get(v___x_3106_, 3);
v_traceState_3111_ = lean_ctor_get(v___x_3106_, 4);
v_recordedDeps_3112_ = lean_ctor_get(v___x_3106_, 6);
v_messages_3113_ = lean_ctor_get(v___x_3106_, 7);
v_infoState_3114_ = lean_ctor_get(v___x_3106_, 8);
v_snapshotTasks_3115_ = lean_ctor_get(v___x_3106_, 9);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v___x_3106_, 5);
lean_dec(v_unused_3145_);
v___x_3117_ = v___x_3106_;
v_isShared_3118_ = v_isSharedCheck_3144_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_snapshotTasks_3115_);
lean_inc(v_infoState_3114_);
lean_inc(v_messages_3113_);
lean_inc(v_recordedDeps_3112_);
lean_inc(v_traceState_3111_);
lean_inc(v_auxDeclNGen_3110_);
lean_inc(v_ngen_3109_);
lean_inc(v_nextMacroScope_3108_);
lean_inc(v_env_3107_);
lean_dec(v___x_3106_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3144_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3119_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_3084_, v_env_3107_, v___f_3105_);
v___x_3120_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 5, v___x_3120_);
lean_ctor_set(v___x_3117_, 0, v___x_3119_);
v___x_3122_ = v___x_3117_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_nextMacroScope_3108_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_ngen_3109_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_auxDeclNGen_3110_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_traceState_3111_);
lean_ctor_set(v_reuseFailAlloc_3143_, 5, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3143_, 6, v_recordedDeps_3112_);
lean_ctor_set(v_reuseFailAlloc_3143_, 7, v_messages_3113_);
lean_ctor_set(v_reuseFailAlloc_3143_, 8, v_infoState_3114_);
lean_ctor_set(v_reuseFailAlloc_3143_, 9, v_snapshotTasks_3115_);
v___x_3122_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v_mctx_3125_; lean_object* v_zetaDeltaFVarIds_3126_; lean_object* v_postponed_3127_; lean_object* v_diag_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3141_; 
v___x_3123_ = lean_st_ref_put(v_a_3089_, v___x_3122_);
v___x_3124_ = lean_st_ref_take(v_a_3087_);
v_mctx_3125_ = lean_ctor_get(v___x_3124_, 0);
v_zetaDeltaFVarIds_3126_ = lean_ctor_get(v___x_3124_, 2);
v_postponed_3127_ = lean_ctor_get(v___x_3124_, 3);
v_diag_3128_ = lean_ctor_get(v___x_3124_, 4);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v___x_3124_, 1);
lean_dec(v_unused_3142_);
v___x_3130_ = v___x_3124_;
v_isShared_3131_ = v_isSharedCheck_3141_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_diag_3128_);
lean_inc(v_postponed_3127_);
lean_inc(v_zetaDeltaFVarIds_3126_);
lean_inc(v_mctx_3125_);
lean_dec(v___x_3124_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3141_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v___x_3133_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_mctx_3125_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3140_, 2, v_zetaDeltaFVarIds_3126_);
lean_ctor_set(v_reuseFailAlloc_3140_, 3, v_postponed_3127_);
lean_ctor_set(v_reuseFailAlloc_3140_, 4, v_diag_3128_);
v___x_3135_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = lean_st_ref_put(v_a_3087_, v___x_3135_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3132_);
v___x_3138_ = v___x_3103_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3132_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v_ext_3084_);
v_a_3147_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3100_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3100_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_3155_, lean_object* v_declName_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3155_, v_declName_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
return v_res_3162_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3163_, lean_object* v_i_3164_, lean_object* v_k_3165_){
_start:
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = lean_array_get_size(v_keys_3163_);
v___x_3167_ = lean_nat_dec_lt(v_i_3164_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_dec(v_i_3164_);
return v___x_3167_;
}
else
{
lean_object* v_k_x27_3168_; uint8_t v___x_3169_; 
v_k_x27_3168_ = lean_array_fget_borrowed(v_keys_3163_, v_i_3164_);
v___x_3169_ = lean_name_eq(v_k_3165_, v_k_x27_3168_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_unsigned_to_nat(1u);
v___x_3171_ = lean_nat_add(v_i_3164_, v___x_3170_);
lean_dec(v_i_3164_);
v_i_3164_ = v___x_3171_;
goto _start;
}
else
{
lean_dec(v_i_3164_);
return v___x_3167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3173_, lean_object* v_i_3174_, lean_object* v_k_3175_){
_start:
{
uint8_t v_res_3176_; lean_object* v_r_3177_; 
v_res_3176_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3173_, v_i_3174_, v_k_3175_);
lean_dec(v_k_3175_);
lean_dec_ref(v_keys_3173_);
v_r_3177_ = lean_box(v_res_3176_);
return v_r_3177_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_3178_, size_t v_x_3179_, lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3178_) == 0)
{
lean_object* v_es_3181_; lean_object* v___x_3182_; size_t v___x_3183_; size_t v___x_3184_; lean_object* v_j_3185_; lean_object* v___x_3186_; 
v_es_3181_ = lean_ctor_get(v_x_3178_, 0);
v___x_3182_ = lean_box(2);
v___x_3183_ = ((size_t)31ULL);
v___x_3184_ = lean_usize_land(v_x_3179_, v___x_3183_);
v_j_3185_ = lean_usize_to_nat(v___x_3184_);
v___x_3186_ = lean_array_get_borrowed(v___x_3182_, v_es_3181_, v_j_3185_);
lean_dec(v_j_3185_);
switch(lean_obj_tag(v___x_3186_))
{
case 0:
{
lean_object* v_key_3187_; uint8_t v___x_3188_; 
v_key_3187_ = lean_ctor_get(v___x_3186_, 0);
v___x_3188_ = lean_name_eq(v_x_3180_, v_key_3187_);
return v___x_3188_;
}
case 1:
{
lean_object* v_node_3189_; size_t v___x_3190_; size_t v___x_3191_; 
v_node_3189_ = lean_ctor_get(v___x_3186_, 0);
v___x_3190_ = ((size_t)5ULL);
v___x_3191_ = lean_usize_shift_right(v_x_3179_, v___x_3190_);
v_x_3178_ = v_node_3189_;
v_x_3179_ = v___x_3191_;
goto _start;
}
default: 
{
uint8_t v___x_3193_; 
v___x_3193_ = 0;
return v___x_3193_;
}
}
}
else
{
lean_object* v_ks_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; 
v_ks_3194_ = lean_ctor_get(v_x_3178_, 0);
v___x_3195_ = lean_unsigned_to_nat(0u);
v___x_3196_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_3194_, v___x_3195_, v_x_3180_);
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_3197_, lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
size_t v_x_330__boxed_3200_; uint8_t v_res_3201_; lean_object* v_r_3202_; 
v_x_330__boxed_3200_ = lean_unbox_usize(v_x_3198_);
lean_dec(v_x_3198_);
v_res_3201_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3197_, v_x_330__boxed_3200_, v_x_3199_);
lean_dec(v_x_3199_);
lean_dec_ref(v_x_3197_);
v_r_3202_ = lean_box(v_res_3201_);
return v_r_3202_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_3203_, lean_object* v_x_3204_){
_start:
{
uint64_t v___y_3206_; 
if (lean_obj_tag(v_x_3204_) == 0)
{
uint64_t v___x_3209_; 
v___x_3209_ = 1723ULL;
v___y_3206_ = v___x_3209_;
goto v___jp_3205_;
}
else
{
uint64_t v_hash_3210_; 
v_hash_3210_ = lean_ctor_get_uint64(v_x_3204_, sizeof(void*)*2);
v___y_3206_ = v_hash_3210_;
goto v___jp_3205_;
}
v___jp_3205_:
{
size_t v___x_3207_; uint8_t v___x_3208_; 
v___x_3207_ = lean_uint64_to_usize(v___y_3206_);
v___x_3208_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3203_, v___x_3207_, v_x_3204_);
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_res_3213_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3211_, v_x_3212_);
lean_dec(v_x_3212_);
lean_dec_ref(v_x_3211_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_3215_, lean_object* v_declName_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v_ext_3221_; lean_object* v_toEnvExtension_3222_; lean_object* v_env_3223_; lean_object* v_asyncMode_3224_; uint8_t v___x_3225_; lean_object* v___x_3226_; lean_object* v_extThms_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3219_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3220_ = lean_st_ref_get(v_a_3217_);
v_ext_3221_ = lean_ctor_get(v_ext_3215_, 1);
v_toEnvExtension_3222_ = lean_ctor_get(v_ext_3221_, 0);
v_env_3223_ = lean_ctor_get(v___x_3220_, 0);
lean_inc_ref(v_env_3223_);
lean_dec(v___x_3220_);
v_asyncMode_3224_ = lean_ctor_get(v_toEnvExtension_3222_, 2);
v___x_3225_ = 0;
v___x_3226_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3219_, v_ext_3215_, v_env_3223_, v_asyncMode_3224_, v___x_3225_);
v_extThms_3227_ = lean_ctor_get(v___x_3226_, 1);
lean_inc_ref(v_extThms_3227_);
lean_dec(v___x_3226_);
v___x_3228_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_3227_, v_declName_3216_);
lean_dec_ref(v_extThms_3227_);
v___x_3229_ = lean_box(v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_3231_, lean_object* v_declName_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3231_, v_declName_3232_, v_a_3233_);
lean_dec(v_a_3233_);
lean_dec(v_declName_3232_);
lean_dec_ref(v_ext_3231_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_3236_, lean_object* v_declName_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3236_, v_declName_3237_, v_a_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_3242_, lean_object* v_declName_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_3242_, v_declName_3243_, v_a_3244_, v_a_3245_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_declName_3243_);
lean_dec_ref(v_ext_3242_);
return v_res_3247_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_3248_, lean_object* v_x_3249_, lean_object* v_x_3250_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_3249_, v_x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
uint8_t v_res_3255_; lean_object* v_r_3256_; 
v_res_3255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_3252_, v_x_3253_, v_x_3254_);
lean_dec(v_x_3254_);
lean_dec_ref(v_x_3253_);
v_r_3256_ = lean_box(v_res_3255_);
return v_r_3256_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_3257_, lean_object* v_x_3258_, size_t v_x_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_3258_, v_x_3259_, v_x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_){
_start:
{
size_t v_x_417__boxed_3266_; uint8_t v_res_3267_; lean_object* v_r_3268_; 
v_x_417__boxed_3266_ = lean_unbox_usize(v_x_3264_);
lean_dec(v_x_3264_);
v_res_3267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_3262_, v_x_3263_, v_x_417__boxed_3266_, v_x_3265_);
lean_dec(v_x_3265_);
lean_dec_ref(v_x_3263_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3269_, lean_object* v_keys_3270_, lean_object* v_vals_3271_, lean_object* v_heq_3272_, lean_object* v_i_3273_, lean_object* v_k_3274_){
_start:
{
uint8_t v___x_3275_; 
v___x_3275_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_3270_, v_i_3273_, v_k_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3276_, lean_object* v_keys_3277_, lean_object* v_vals_3278_, lean_object* v_heq_3279_, lean_object* v_i_3280_, lean_object* v_k_3281_){
_start:
{
uint8_t v_res_3282_; lean_object* v_r_3283_; 
v_res_3282_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_3276_, v_keys_3277_, v_vals_3278_, v_heq_3279_, v_i_3280_, v_k_3281_);
lean_dec(v_k_3281_);
lean_dec_ref(v_vals_3278_);
lean_dec_ref(v_keys_3277_);
v_r_3283_ = lean_box(v_res_3282_);
return v_r_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_3284_, lean_object* v_declName_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v_ext_3290_; lean_object* v_toEnvExtension_3291_; lean_object* v_env_3292_; lean_object* v_asyncMode_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v_inj_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3288_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3289_ = lean_st_ref_get(v_a_3286_);
v_ext_3290_ = lean_ctor_get(v_ext_3284_, 1);
v_toEnvExtension_3291_ = lean_ctor_get(v_ext_3290_, 0);
v_env_3292_ = lean_ctor_get(v___x_3289_, 0);
lean_inc_ref(v_env_3292_);
lean_dec(v___x_3289_);
v_asyncMode_3293_ = lean_ctor_get(v_toEnvExtension_3291_, 2);
v___x_3294_ = 0;
v___x_3295_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3288_, v_ext_3284_, v_env_3292_, v_asyncMode_3293_, v___x_3294_);
v_inj_3296_ = lean_ctor_get(v___x_3295_, 4);
lean_inc_ref(v_inj_3296_);
lean_dec(v___x_3295_);
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v_declName_3285_);
v___x_3298_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_3296_, v___x_3297_);
lean_dec_ref_known(v___x_3297_, 1);
lean_dec_ref(v_inj_3296_);
v___x_3299_ = lean_box(v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_3301_, lean_object* v_declName_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3301_, v_declName_3302_, v_a_3303_);
lean_dec(v_a_3303_);
lean_dec_ref(v_ext_3301_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_3306_, lean_object* v_declName_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3306_, v_declName_3307_, v_a_3309_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_3312_, lean_object* v_declName_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_3312_, v_declName_3313_, v_a_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec_ref(v_ext_3312_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_3318_, lean_object* v_declName_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v_ext_3324_; lean_object* v_toEnvExtension_3325_; lean_object* v_env_3326_; lean_object* v_asyncMode_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v_funCC_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3322_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_3323_ = lean_st_ref_get(v_a_3320_);
v_ext_3324_ = lean_ctor_get(v_ext_3318_, 1);
v_toEnvExtension_3325_ = lean_ctor_get(v_ext_3324_, 0);
v_env_3326_ = lean_ctor_get(v___x_3323_, 0);
lean_inc_ref(v_env_3326_);
lean_dec(v___x_3323_);
v_asyncMode_3327_ = lean_ctor_get(v_toEnvExtension_3325_, 2);
v___x_3328_ = 0;
v___x_3329_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3322_, v_ext_3318_, v_env_3326_, v_asyncMode_3327_, v___x_3328_);
v_funCC_3330_ = lean_ctor_get(v___x_3329_, 2);
lean_inc(v_funCC_3330_);
lean_dec(v___x_3329_);
v___x_3331_ = l_Lean_NameSet_contains(v_funCC_3330_, v_declName_3319_);
lean_dec(v_funCC_3330_);
v___x_3332_ = lean_box(v___x_3331_);
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_3334_, lean_object* v_declName_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3334_, v_declName_3335_, v_a_3336_);
lean_dec(v_a_3336_);
lean_dec(v_declName_3335_);
lean_dec_ref(v_ext_3334_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_3339_, lean_object* v_declName_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3339_, v_declName_3340_, v_a_3342_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_3345_, lean_object* v_declName_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_3345_, v_declName_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_declName_3346_);
lean_dec_ref(v_ext_3345_);
return v_res_3350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_3375_ = l_Lean_mkAtom(v___x_3374_);
return v___x_3375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3378_ = lean_array_push(v___x_3377_, v___x_3376_);
return v___x_3378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_3388_ = l_Lean_mkAtom(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3391_ = lean_array_push(v___x_3390_, v___x_3389_);
return v___x_3391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_3394_ = lean_box(2);
v___x_3395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___x_3393_);
lean_ctor_set(v___x_3395_, 2, v___x_3392_);
return v___x_3395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_3397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_3398_ = lean_array_push(v___x_3397_, v___x_3396_);
return v___x_3398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_3401_ = lean_box(2);
v___x_3402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3400_);
lean_ctor_set(v___x_3402_, 2, v___x_3399_);
return v___x_3402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3405_ = lean_array_push(v___x_3404_, v___x_3403_);
return v___x_3405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_3408_ = lean_box(2);
v___x_3409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
lean_ctor_set(v___x_3409_, 1, v___x_3407_);
lean_ctor_set(v___x_3409_, 2, v___x_3406_);
return v___x_3409_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3412_ = lean_array_push(v___x_3411_, v___x_3410_);
return v___x_3412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_3415_ = lean_box(2);
v___x_3416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___x_3414_);
lean_ctor_set(v___x_3416_, 2, v___x_3413_);
return v___x_3416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_3418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_3419_ = lean_array_push(v___x_3418_, v___x_3417_);
return v___x_3419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_3421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_3422_ = lean_box(2);
v___x_3423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v___x_3421_);
lean_ctor_set(v___x_3423_, 2, v___x_3420_);
return v___x_3423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_3425_, lean_object* v_ext_3426_, lean_object* v_____r_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
uint8_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = 0;
lean_inc(v_declName_3425_);
v___x_3434_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_3425_, v___x_3433_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; uint8_t v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v_a_3438_; uint8_t v___x_3439_; 
v___x_3437_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_3426_, v_declName_3425_, v___y_3431_);
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = lean_unbox(v_a_3438_);
lean_dec(v_a_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v_a_3441_; uint8_t v___x_3442_; 
lean_inc(v_declName_3425_);
v___x_3440_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_3426_, v_declName_3425_, v___y_3431_);
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref(v___x_3440_);
v___x_3442_ = lean_unbox(v_a_3441_);
lean_dec(v_a_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v_a_3444_; uint8_t v___x_3445_; 
v___x_3443_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_3426_, v_declName_3425_, v___y_3431_);
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = lean_unbox(v_a_3444_);
lean_dec(v_a_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_3426_, v_declName_3425_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3446_;
}
else
{
lean_object* v___x_3447_; 
v___x_3447_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_3426_, v_declName_3425_, v___y_3430_, v___y_3431_);
return v___x_3447_;
}
}
else
{
lean_object* v___x_3448_; 
v___x_3448_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_3426_, v_declName_3425_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3448_;
}
}
else
{
lean_object* v___x_3449_; 
v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_3426_, v_declName_3425_, v___y_3430_, v___y_3431_);
return v___x_3449_;
}
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_3426_, v_declName_3425_, v___y_3430_, v___y_3431_);
return v___x_3450_;
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v_ext_3426_);
lean_dec(v_declName_3425_);
v_a_3451_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3434_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3434_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_3459_, lean_object* v_ext_3460_, lean_object* v_____r_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3459_, v_ext_3460_, v_____r_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_ref_3474_; lean_object* v___x_3475_; lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3484_; 
v_ref_3474_ = lean_ctor_get(v___y_3471_, 2);
v___x_3475_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0_spec__0(v_msg_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3484_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3484_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
lean_inc(v_ref_3474_);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v_ref_3474_);
lean_ctor_set(v___x_3480_, 1, v_a_3476_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set_tag(v___x_3478_, 1);
lean_ctor_set(v___x_3478_, 0, v___x_3480_);
v___x_3482_ = v___x_3478_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
return v_res_3491_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3498_; uint64_t v___x_3499_; 
v___x_3498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3499_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_3501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_3502_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set_uint64(v___x_3502_, sizeof(void*)*1, v___x_3500_);
return v___x_3502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default___closed__0);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3505_ = lean_box(1);
v___x_3506_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set(v___x_3508_, 1, v___x_3506_);
lean_ctor_set(v___x_3508_, 2, v___x_3505_);
return v___x_3508_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3511_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
lean_ctor_set(v___x_3514_, 2, v___x_3513_);
lean_ctor_set(v___x_3514_, 3, v___x_3513_);
lean_ctor_set(v___x_3514_, 4, v___x_3512_);
lean_ctor_set(v___x_3514_, 5, v___x_3512_);
lean_ctor_set(v___x_3514_, 6, v___x_3512_);
lean_ctor_set(v___x_3514_, 7, v___x_3512_);
lean_ctor_set(v___x_3514_, 8, v___x_3512_);
lean_ctor_set(v___x_3514_, 9, v___x_3512_);
lean_ctor_set(v___x_3514_, 10, v___x_3512_);
lean_ctor_set(v___x_3514_, 11, v___x_3511_);
return v___x_3514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3516_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__2);
v___x_3517_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v___x_3515_);
lean_ctor_set(v___x_3517_, 2, v___x_3515_);
lean_ctor_set(v___x_3517_, 3, v___x_3515_);
lean_ctor_set(v___x_3517_, 4, v___x_3515_);
lean_ctor_set(v___x_3517_, 5, v___x_3515_);
lean_ctor_set(v___x_3517_, 6, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_3519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
lean_ctor_set(v___x_3519_, 2, v___x_3518_);
lean_ctor_set(v___x_3519_, 3, v___x_3518_);
lean_ctor_set(v___x_3519_, 4, v___x_3518_);
return v___x_3519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_3525_ = l_Lean_stringToMessageData(v___x_3524_);
return v___x_3525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_3528_ = l_Lean_stringToMessageData(v___x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_3529_, lean_object* v___x_3530_, uint8_t v_showInfo_3531_, lean_object* v_attrName_3532_, lean_object* v_declName_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
uint8_t v___x_3537_; uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___y_3552_; 
v___x_3537_ = 1;
v___x_3538_ = 0;
v___x_3539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_3542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3544_ = lean_box(0);
lean_inc(v___x_3530_);
v___x_3545_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3545_, 0, v___x_3539_);
lean_ctor_set(v___x_3545_, 1, v___x_3530_);
lean_ctor_set(v___x_3545_, 2, v___x_3542_);
lean_ctor_set(v___x_3545_, 3, v___x_3543_);
lean_ctor_set(v___x_3545_, 4, v___x_3544_);
lean_ctor_set(v___x_3545_, 5, v___x_3540_);
lean_ctor_set(v___x_3545_, 6, v___x_3544_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*7, v___x_3538_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*7 + 1, v___x_3538_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*7 + 2, v___x_3538_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*7 + 3, v___x_3537_);
v___x_3546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3546_);
lean_ctor_set(v___x_3549_, 1, v___x_3547_);
lean_ctor_set(v___x_3549_, 2, v___x_3530_);
lean_ctor_set(v___x_3549_, 3, v___x_3541_);
lean_ctor_set(v___x_3549_, 4, v___x_3548_);
v___x_3550_ = lean_st_mk_ref(v___x_3549_);
if (v_showInfo_3531_ == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec(v_attrName_3532_);
v___x_3562_ = lean_box(0);
v___x_3563_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_3533_, v_ext_3529_, v___x_3562_, v___x_3545_, v___x_3550_, v___y_3534_, v___y_3535_);
lean_dec_ref_known(v___x_3545_, 7);
v___y_3552_ = v___x_3563_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_dec(v_declName_3533_);
lean_dec_ref(v_ext_3529_);
v___x_3564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_3565_ = l_Lean_MessageData_ofName(v_attrName_3532_);
lean_inc_ref(v___x_3565_);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
lean_ctor_set(v___x_3569_, 1, v___x_3565_);
v___x_3570_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3571_, v___x_3545_, v___x_3550_, v___y_3534_, v___y_3535_);
lean_dec(v___x_3550_);
lean_dec_ref_known(v___x_3545_, 7);
return v___x_3572_;
}
v___jp_3551_:
{
if (lean_obj_tag(v___y_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3561_; 
v_a_3553_ = lean_ctor_get(v___y_3552_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___y_3552_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3555_ = v___y_3552_;
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___y_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_st_ref_get(v___x_3550_);
lean_dec(v___x_3550_);
lean_dec(v___x_3557_);
if (v_isShared_3556_ == 0)
{
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3553_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_dec(v___x_3550_);
return v___y_3552_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_3573_, lean_object* v___x_3574_, lean_object* v_showInfo_3575_, lean_object* v_attrName_3576_, lean_object* v_declName_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v_showInfo_boxed_3581_; lean_object* v_res_3582_; 
v_showInfo_boxed_3581_ = lean_unbox(v_showInfo_3575_);
v_res_3582_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_3573_, v___x_3574_, v_showInfo_boxed_3581_, v_attrName_3576_, v_declName_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_3585_, uint8_t v_attrKind_3586_, uint8_t v_showInfo_3587_, uint8_t v_minIndexable_3588_, lean_object* v_as_x27_3589_, lean_object* v_b_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
if (lean_obj_tag(v_as_x27_3589_) == 0)
{
lean_object* v___x_3596_; 
lean_dec_ref(v_ext_3585_);
v___x_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3596_, 0, v_b_3590_);
return v___x_3596_;
}
else
{
lean_object* v_head_3597_; lean_object* v_tail_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v_head_3597_ = lean_ctor_get(v_as_x27_3589_, 0);
v_tail_3598_ = lean_ctor_get(v_as_x27_3589_, 1);
v___x_3599_ = lean_box(0);
v___x_3600_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3594_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_3597_);
lean_inc_ref(v_ext_3585_);
v___x_3603_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3585_, v_head_3597_, v_attrKind_3586_, v___x_3602_, v_a_3601_, v_showInfo_3587_, v_minIndexable_3588_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_dec_ref_known(v___x_3603_, 1);
v_as_x27_3589_ = v_tail_3598_;
v_b_3590_ = v___x_3599_;
goto _start;
}
else
{
lean_dec_ref(v_ext_3585_);
return v___x_3603_;
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec_ref(v_ext_3585_);
v_a_3605_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3600_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3600_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_3613_, lean_object* v_attrKind_3614_, lean_object* v_showInfo_3615_, lean_object* v_minIndexable_3616_, lean_object* v_as_x27_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
uint8_t v_attrKind_boxed_3624_; uint8_t v_showInfo_boxed_3625_; uint8_t v_minIndexable_boxed_3626_; lean_object* v_res_3627_; 
v_attrKind_boxed_3624_ = lean_unbox(v_attrKind_3614_);
v_showInfo_boxed_3625_ = lean_unbox(v_showInfo_3615_);
v_minIndexable_boxed_3626_ = lean_unbox(v_minIndexable_3616_);
v_res_3627_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3613_, v_attrKind_boxed_3624_, v_showInfo_boxed_3625_, v_minIndexable_boxed_3626_, v_as_x27_3617_, v_b_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v_as_x27_3617_);
return v_res_3627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_3630_ = l_Lean_stringToMessageData(v___x_3629_);
return v___x_3630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_3633_ = l_Lean_stringToMessageData(v___x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v___x_3636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_3639_ = l_Lean_stringToMessageData(v___x_3638_);
return v___x_3639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
return v___x_3644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_3647_ = l_Lean_stringToMessageData(v___x_3646_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_3657_, uint8_t v_attrKind_3658_, lean_object* v_stx_3659_, lean_object* v_ext_3660_, uint8_t v_showInfo_3661_, uint8_t v_minIndexable_3662_, uint8_t v___x_3663_, lean_object* v_attrName_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_3659_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
switch(lean_obj_tag(v_a_3693_))
{
case 0:
{
lean_object* v_k_3694_; 
lean_dec(v_attrName_3664_);
lean_dec(v_stx_3659_);
v_k_3694_ = lean_ctor_get(v_a_3693_, 0);
lean_inc(v_k_3694_);
lean_dec_ref_known(v_a_3693_, 1);
if (lean_obj_tag(v_k_3694_) == 9)
{
lean_object* v___x_3695_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_declName_3657_);
v___x_3695_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_3667_, v___y_3668_);
return v___x_3695_;
}
else
{
lean_object* v___x_3696_; 
v___x_3696_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3668_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3698_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3696_, 1);
v___x_3698_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_3660_, v_declName_3657_, v_attrKind_3658_, v_k_3694_, v_a_3697_, v_showInfo_3661_, v_minIndexable_3662_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_k_3694_);
lean_dec_ref(v_ext_3660_);
lean_dec(v_declName_3657_);
v_a_3699_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3696_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3696_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_3707_; lean_object* v___x_3708_; 
lean_dec(v_attrName_3664_);
lean_dec(v_stx_3659_);
v_eager_3707_ = lean_ctor_get_uint8(v_a_3693_, 0);
lean_dec_ref_known(v_a_3693_, 0);
v___x_3708_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3660_, v_declName_3657_, v_eager_3707_, v_attrKind_3658_, v___y_3667_, v___y_3668_);
return v___x_3708_;
}
case 2:
{
lean_object* v___x_3709_; 
lean_dec(v_stx_3659_);
lean_inc(v_declName_3657_);
v___x_3709_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_3657_, v___x_3663_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
if (lean_obj_tag(v_a_3710_) == 1)
{
lean_object* v_val_3711_; lean_object* v_ctors_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_dec(v_attrName_3664_);
lean_dec(v_declName_3657_);
v_val_3711_ = lean_ctor_get(v_a_3710_, 0);
lean_inc(v_val_3711_);
lean_dec_ref_known(v_a_3710_, 1);
v_ctors_3712_ = lean_ctor_get(v_val_3711_, 4);
lean_inc(v_ctors_3712_);
lean_dec(v_val_3711_);
v___x_3713_ = lean_box(0);
v___x_3714_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3660_, v_attrKind_3658_, v_showInfo_3661_, v_minIndexable_3662_, v_ctors_3712_, v___x_3713_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v_ctors_3712_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3721_ == 0)
{
lean_object* v_unused_3722_; 
v_unused_3722_ = lean_ctor_get(v___x_3714_, 0);
lean_dec(v_unused_3722_);
v___x_3716_ = v___x_3714_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_dec(v___x_3714_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3713_);
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3713_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
else
{
return v___x_3714_;
}
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
lean_dec(v_a_3710_);
lean_dec_ref(v_ext_3660_);
v___x_3723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_3724_ = l_Lean_MessageData_ofName(v_attrName_3664_);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = l_Lean_MessageData_ofConstName(v_declName_3657_, v___x_3663_);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3731_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3732_;
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v_attrName_3664_);
lean_dec_ref(v_ext_3660_);
lean_dec(v_declName_3657_);
v_a_3733_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3709_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3709_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
case 3:
{
lean_object* v___x_3741_; 
lean_dec(v_attrName_3664_);
lean_inc(v_declName_3657_);
v___x_3741_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_3657_, v___x_3663_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3742_);
lean_dec_ref_known(v___x_3741_, 1);
if (lean_obj_tag(v_a_3742_) == 1)
{
lean_object* v_val_3743_; lean_object* v___x_3744_; 
lean_dec(v_stx_3659_);
lean_dec(v_declName_3657_);
v_val_3743_ = lean_ctor_get(v_a_3742_, 0);
lean_inc_n(v_val_3743_, 2);
lean_dec_ref_known(v_a_3742_, 1);
lean_inc_ref(v_ext_3660_);
v___x_3744_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_3660_, v_val_3743_, v___x_3663_, v_attrKind_3658_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v___x_3745_; 
lean_dec_ref_known(v___x_3744_, 1);
v___x_3745_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3743_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3766_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3766_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3766_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
if (lean_obj_tag(v_a_3746_) == 1)
{
lean_object* v_val_3750_; lean_object* v_ctors_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_del_object(v___x_3748_);
v_val_3750_ = lean_ctor_get(v_a_3746_, 0);
lean_inc(v_val_3750_);
lean_dec_ref_known(v_a_3746_, 1);
v_ctors_3751_ = lean_ctor_get(v_val_3750_, 4);
lean_inc(v_ctors_3751_);
lean_dec(v_val_3750_);
v___x_3752_ = lean_box(0);
v___x_3753_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3660_, v_attrKind_3658_, v_showInfo_3661_, v_minIndexable_3662_, v_ctors_3751_, v___x_3752_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v_ctors_3751_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3760_ == 0)
{
lean_object* v_unused_3761_; 
v_unused_3761_ = lean_ctor_get(v___x_3753_, 0);
lean_dec(v_unused_3761_);
v___x_3755_ = v___x_3753_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_dec(v___x_3753_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3752_);
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3752_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
else
{
return v___x_3753_;
}
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
lean_dec(v_a_3746_);
lean_dec_ref(v_ext_3660_);
v___x_3762_ = lean_box(0);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3762_);
v___x_3764_ = v___x_3748_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref(v_ext_3660_);
v_a_3767_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3745_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3745_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_dec(v_val_3743_);
lean_dec_ref(v_ext_3660_);
return v___x_3744_;
}
}
else
{
lean_object* v___x_3775_; 
lean_dec(v_a_3742_);
v___x_3775_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_3668_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v___x_3777_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_3660_, v_stx_3659_, v_declName_3657_, v_attrKind_3658_, v_a_3776_, v_minIndexable_3662_, v_showInfo_3661_, v___x_3663_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3777_;
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
lean_dec(v_declName_3657_);
v_a_3778_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3775_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3775_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
lean_dec(v_declName_3657_);
v_a_3786_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3741_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3741_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
case 4:
{
lean_object* v___x_3794_; 
lean_dec(v_attrName_3664_);
lean_dec(v_stx_3659_);
v___x_3794_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_3660_, v_declName_3657_, v_attrKind_3658_, v___y_3667_, v___y_3668_);
return v___x_3794_;
}
case 5:
{
lean_object* v_prio_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
v_prio_3795_ = lean_ctor_get(v_a_3693_, 0);
lean_inc(v_prio_3795_);
lean_dec_ref_known(v_a_3693_, 1);
v___x_3796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3797_ = lean_name_eq(v_attrName_3664_, v___x_3796_);
lean_dec(v_attrName_3664_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec(v_prio_3795_);
lean_dec(v_declName_3657_);
v___x_3798_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10);
v___x_3799_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3798_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3799_;
}
else
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_3657_, v_attrKind_3658_, v_prio_3795_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3800_;
}
}
case 6:
{
lean_object* v___x_3801_; 
lean_dec(v_attrName_3664_);
lean_dec(v_stx_3659_);
v___x_3801_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_3660_, v_declName_3657_, v_attrKind_3658_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3801_;
}
case 7:
{
lean_object* v___x_3802_; 
lean_dec(v_attrName_3664_);
lean_dec(v_stx_3659_);
v___x_3802_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_3660_, v_declName_3657_, v_attrKind_3658_, v___y_3667_, v___y_3668_);
return v___x_3802_;
}
case 8:
{
uint8_t v_post_3803_; uint8_t v_inv_3804_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
v_post_3803_ = lean_ctor_get_uint8(v_a_3693_, 0);
v_inv_3804_ = lean_ctor_get_uint8(v_a_3693_, 1);
lean_dec_ref_known(v_a_3693_, 0);
v___x_3812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3813_ = lean_name_eq(v_attrName_3664_, v___x_3812_);
lean_dec(v_attrName_3664_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_dec(v_declName_3657_);
v___x_3814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12);
v___x_3815_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3814_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3815_;
}
else
{
v___y_3806_ = v___y_3665_;
v___y_3807_ = v___y_3666_;
v___y_3808_ = v___y_3667_;
v___y_3809_ = v___y_3668_;
goto v___jp_3805_;
}
v___jp_3805_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = lean_unsigned_to_nat(1000u);
v___x_3811_ = l_Lean_Meta_Grind_addNormTheorem(v_declName_3657_, v_post_3803_, v_inv_3804_, v_attrKind_3658_, v___x_3810_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
return v___x_3811_;
}
}
case 9:
{
lean_object* v___x_3816_; uint8_t v___x_3817_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
v___x_3816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3817_ = lean_name_eq(v_attrName_3664_, v___x_3816_);
lean_dec(v_attrName_3664_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_dec(v_declName_3657_);
v___x_3818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14);
v___x_3819_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3818_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3819_;
}
else
{
goto v___jp_3670_;
}
}
case 10:
{
uint8_t v_fallback_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
v_fallback_3820_ = lean_ctor_get_uint8(v_a_3693_, 0);
lean_dec_ref_known(v_a_3693_, 0);
v___x_3821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3822_ = lean_name_eq(v_attrName_3664_, v___x_3821_);
lean_dec(v_attrName_3664_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
lean_dec(v_declName_3657_);
v___x_3823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16);
v___x_3824_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3823_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3824_;
}
else
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_3657_, v_attrKind_3658_, v_fallback_3820_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3825_;
}
}
default: 
{
lean_object* v___x_3826_; uint8_t v___x_3827_; 
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
v___x_3826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_3827_ = lean_name_eq(v_attrName_3664_, v___x_3826_);
lean_dec(v_attrName_3664_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
lean_dec(v_declName_3657_);
v___x_3828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18);
v___x_3829_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3828_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3829_;
}
else
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_3657_, v_attrKind_3658_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3830_;
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec(v_attrName_3664_);
lean_dec_ref(v_ext_3660_);
lean_dec(v_stx_3659_);
lean_dec(v_declName_3657_);
v_a_3831_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3692_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3692_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
v___jp_3670_:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_Meta_Grind_addNormDeclToUnfold(v_declName_3657_, v_attrKind_3658_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3683_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3683_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3683_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
uint8_t v___x_3676_; 
v___x_3676_ = lean_unbox(v_a_3672_);
lean_dec(v_a_3672_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_del_object(v___x_3674_);
v___x_3677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_3678_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_3677_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3678_;
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3679_ = lean_box(0);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3679_);
v___x_3681_ = v___x_3674_;
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
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
v_a_3684_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3671_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3671_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_3839_, lean_object* v_attrKind_3840_, lean_object* v_stx_3841_, lean_object* v_ext_3842_, lean_object* v_showInfo_3843_, lean_object* v_minIndexable_3844_, lean_object* v___x_3845_, lean_object* v_attrName_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
uint8_t v_attrKind_boxed_3852_; uint8_t v_showInfo_boxed_3853_; uint8_t v_minIndexable_boxed_3854_; uint8_t v___x_11455__boxed_3855_; lean_object* v_res_3856_; 
v_attrKind_boxed_3852_ = lean_unbox(v_attrKind_3840_);
v_showInfo_boxed_3853_ = lean_unbox(v_showInfo_3843_);
v_minIndexable_boxed_3854_ = lean_unbox(v_minIndexable_3844_);
v___x_11455__boxed_3855_ = lean_unbox(v___x_3845_);
v_res_3856_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_3839_, v_attrKind_boxed_3852_, v_stx_3841_, v_ext_3842_, v_showInfo_boxed_3853_, v_minIndexable_boxed_3854_, v___x_11455__boxed_3855_, v_attrName_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0(lean_object* v___x_3857_, lean_object* v_entry_3858_, lean_object* v_s_3859_){
_start:
{
lean_object* v_addEntryFn_3860_; lean_object* v_importedEntries_3861_; lean_object* v_state_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3870_; 
v_addEntryFn_3860_ = lean_ctor_get(v___x_3857_, 3);
lean_inc(v_addEntryFn_3860_);
lean_dec_ref(v___x_3857_);
v_importedEntries_3861_ = lean_ctor_get(v_s_3859_, 0);
v_state_3862_ = lean_ctor_get(v_s_3859_, 1);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_s_3859_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3864_ = v_s_3859_;
v_isShared_3865_ = v_isSharedCheck_3870_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_state_3862_);
lean_inc(v_importedEntries_3861_);
lean_dec(v_s_3859_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3870_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v_state_3866_; lean_object* v___x_3868_; 
v_state_3866_ = lean_apply_2(v_addEntryFn_3860_, v_state_3862_, v_entry_3858_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v_state_3866_);
v___x_3868_ = v___x_3864_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_importedEntries_3861_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_state_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_keys_3871_, lean_object* v_i_3872_, lean_object* v_k_3873_){
_start:
{
lean_object* v___x_3874_; uint8_t v___x_3875_; 
v___x_3874_ = lean_array_get_size(v_keys_3871_);
v___x_3875_ = lean_nat_dec_lt(v_i_3872_, v___x_3874_);
if (v___x_3875_ == 0)
{
lean_dec(v_i_3872_);
return v___x_3875_;
}
else
{
lean_object* v_k_x27_3876_; uint8_t v___x_3877_; 
v_k_x27_3876_ = lean_array_fget_borrowed(v_keys_3871_, v_i_3872_);
v___x_3877_ = l_Lean_instBEqExtraModUse_beq(v_k_3873_, v_k_x27_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_unsigned_to_nat(1u);
v___x_3879_ = lean_nat_add(v_i_3872_, v___x_3878_);
lean_dec(v_i_3872_);
v_i_3872_ = v___x_3879_;
goto _start;
}
else
{
lean_dec(v_i_3872_);
return v___x_3875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_keys_3881_, lean_object* v_i_3882_, lean_object* v_k_3883_){
_start:
{
uint8_t v_res_3884_; lean_object* v_r_3885_; 
v_res_3884_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_3881_, v_i_3882_, v_k_3883_);
lean_dec_ref(v_k_3883_);
lean_dec_ref(v_keys_3881_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3886_, size_t v_x_3887_, lean_object* v_x_3888_){
_start:
{
if (lean_obj_tag(v_x_3886_) == 0)
{
lean_object* v_es_3889_; lean_object* v___x_3890_; size_t v___x_3891_; size_t v___x_3892_; lean_object* v_j_3893_; lean_object* v___x_3894_; 
v_es_3889_ = lean_ctor_get(v_x_3886_, 0);
v___x_3890_ = lean_box(2);
v___x_3891_ = ((size_t)31ULL);
v___x_3892_ = lean_usize_land(v_x_3887_, v___x_3891_);
v_j_3893_ = lean_usize_to_nat(v___x_3892_);
v___x_3894_ = lean_array_get_borrowed(v___x_3890_, v_es_3889_, v_j_3893_);
lean_dec(v_j_3893_);
switch(lean_obj_tag(v___x_3894_))
{
case 0:
{
lean_object* v_key_3895_; uint8_t v___x_3896_; 
v_key_3895_ = lean_ctor_get(v___x_3894_, 0);
v___x_3896_ = l_Lean_instBEqExtraModUse_beq(v_x_3888_, v_key_3895_);
return v___x_3896_;
}
case 1:
{
lean_object* v_node_3897_; size_t v___x_3898_; size_t v___x_3899_; 
v_node_3897_ = lean_ctor_get(v___x_3894_, 0);
v___x_3898_ = ((size_t)5ULL);
v___x_3899_ = lean_usize_shift_right(v_x_3887_, v___x_3898_);
v_x_3886_ = v_node_3897_;
v_x_3887_ = v___x_3899_;
goto _start;
}
default: 
{
uint8_t v___x_3901_; 
v___x_3901_ = 0;
return v___x_3901_;
}
}
}
else
{
lean_object* v_ks_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v_ks_3902_ = lean_ctor_get(v_x_3886_, 0);
v___x_3903_ = lean_unsigned_to_nat(0u);
v___x_3904_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_ks_3902_, v___x_3903_, v_x_3888_);
return v___x_3904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_3905_, lean_object* v_x_3906_, lean_object* v_x_3907_){
_start:
{
size_t v_x_11881__boxed_3908_; uint8_t v_res_3909_; lean_object* v_r_3910_; 
v_x_11881__boxed_3908_ = lean_unbox_usize(v_x_3906_);
lean_dec(v_x_3906_);
v_res_3909_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3905_, v_x_11881__boxed_3908_, v_x_3907_);
lean_dec_ref(v_x_3907_);
lean_dec_ref(v_x_3905_);
v_r_3910_ = lean_box(v_res_3909_);
return v_r_3910_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3911_, lean_object* v_x_3912_){
_start:
{
uint64_t v___x_3913_; size_t v___x_3914_; uint8_t v___x_3915_; 
v___x_3913_ = l_Lean_instHashableExtraModUse_hash(v_x_3912_);
v___x_3914_ = lean_uint64_to_usize(v___x_3913_);
v___x_3915_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_3911_, v___x_3914_, v_x_3912_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3916_, lean_object* v_x_3917_){
_start:
{
uint8_t v_res_3918_; lean_object* v_r_3919_; 
v_res_3918_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_3916_, v_x_3917_);
lean_dec_ref(v_x_3917_);
lean_dec_ref(v_x_3916_);
v_r_3919_ = lean_box(v_res_3918_);
return v_r_3919_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_3920_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__3));
v___x_3926_ = l_Lean_stringToMessageData(v___x_3925_);
return v___x_3926_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6(void){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__5));
v___x_3929_ = l_Lean_stringToMessageData(v___x_3928_);
return v___x_3929_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_3931_ = l_Lean_stringToMessageData(v___x_3930_);
return v___x_3931_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8(void){
_start:
{
lean_object* v_cls_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_cls_3932_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_3933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f___closed__1));
v___x_3934_ = l_Lean_Name_append(v___x_3933_, v_cls_3932_);
return v___x_3934_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__9));
v___x_3937_ = l_Lean_stringToMessageData(v___x_3936_);
return v___x_3937_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__11));
v___x_3940_ = l_Lean_stringToMessageData(v___x_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(lean_object* v_mod_3945_, uint8_t v_isMeta_3946_, lean_object* v_hint_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v_env_3987_; uint8_t v_isExporting_3988_; lean_object* v_entry_3989_; lean_object* v___x_3990_; lean_object* v_env_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; 
v___x_3985_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_3986_ = lean_st_ref_get(v___y_3951_);
v_env_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc_ref(v_env_3987_);
lean_dec(v___x_3986_);
v_isExporting_3988_ = lean_ctor_get_uint8(v_env_3987_, sizeof(void*)*13);
lean_dec_ref(v_env_3987_);
lean_inc(v_mod_3945_);
v_entry_3989_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3989_, 0, v_mod_3945_);
lean_ctor_set_uint8(v_entry_3989_, sizeof(void*)*1, v_isExporting_3988_);
lean_ctor_set_uint8(v_entry_3989_, sizeof(void*)*1 + 1, v_isMeta_3946_);
v___x_3990_ = lean_st_ref_get(v___y_3951_);
v_env_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc_ref(v_env_3991_);
lean_dec(v___x_3990_);
v___x_3992_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3993_ = lean_box(1);
v___x_3994_ = lean_box(0);
v___x_3995_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3985_, v___x_3992_, v_env_3991_, v___x_3993_, v___x_3994_);
v___x_3996_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_3995_, v_entry_3989_);
lean_dec(v___x_3995_);
if (v___x_3996_ == 0)
{
lean_object* v_toCold_3997_; lean_object* v_options_3998_; lean_object* v_inheritedTraceOptions_3999_; uint8_t v_hasTrace_4000_; lean_object* v___f_4001_; uint8_t v___x_4002_; lean_object* v___y_4004_; lean_object* v___y_4005_; 
v_toCold_3997_ = lean_ctor_get(v___y_3950_, 0);
v_options_3998_ = lean_ctor_get(v_toCold_3997_, 2);
v_inheritedTraceOptions_3999_ = lean_ctor_get(v_toCold_3997_, 11);
v_hasTrace_4000_ = lean_ctor_get_uint8(v_options_3998_, sizeof(void*)*1);
v___f_4001_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4001_, 0, v___x_3992_);
lean_closure_set(v___f_4001_, 1, v_entry_3989_);
v___x_4002_ = 1;
if (v_hasTrace_4000_ == 0)
{
lean_dec(v_hint_3947_);
lean_dec(v_mod_3945_);
v___y_4004_ = v___y_3949_;
v___y_4005_ = v___y_3951_;
goto v___jp_4003_;
}
else
{
lean_object* v_cls_4032_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v_cls_4032_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4052_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3999_, v_options_3998_, v___x_4052_);
if (v___x_4053_ == 0)
{
lean_dec(v_hint_3947_);
lean_dec(v_mod_3945_);
v___y_4004_ = v___y_3949_;
v___y_4005_ = v___y_3951_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4054_; lean_object* v___y_4056_; 
v___x_4054_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_3988_ == 0)
{
lean_object* v___x_4063_; 
v___x_4063_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4056_ = v___x_4063_;
goto v___jp_4055_;
}
else
{
lean_object* v___x_4064_; 
v___x_4064_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4056_ = v___x_4064_;
goto v___jp_4055_;
}
v___jp_4055_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_inc_ref(v___y_4056_);
v___x_4057_ = l_Lean_stringToMessageData(v___y_4056_);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4054_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4058_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
if (v_isMeta_3946_ == 0)
{
lean_object* v___x_4061_; 
v___x_4061_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4039_ = v___x_4060_;
v___y_4040_ = v___x_4061_;
goto v___jp_4038_;
}
else
{
lean_object* v___x_4062_; 
v___x_4062_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4039_ = v___x_4060_;
v___y_4040_ = v___x_4062_;
goto v___jp_4038_;
}
}
}
v___jp_4033_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___y_4034_);
lean_ctor_set(v___x_4036_, 1, v___y_4035_);
v___x_4037_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0(v_cls_4032_, v___x_4036_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_dec_ref_known(v___x_4037_, 1);
v___y_4004_ = v___y_3949_;
v___y_4005_ = v___y_3951_;
goto v___jp_4003_;
}
else
{
lean_dec_ref(v___f_4001_);
return v___x_4037_;
}
}
v___jp_4038_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
lean_inc_ref(v___y_4040_);
v___x_4041_ = l_Lean_stringToMessageData(v___y_4040_);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___y_4039_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4042_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
v___x_4045_ = l_Lean_MessageData_ofName(v_mod_3945_);
v___x_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4044_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
v___x_4047_ = l_Lean_Name_isAnonymous(v_hint_3947_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4049_ = l_Lean_MessageData_ofName(v_hint_3947_);
v___x_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4048_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___y_4034_ = v___x_4046_;
v___y_4035_ = v___x_4050_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4051_; 
lean_dec(v_hint_3947_);
v___x_4051_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4034_ = v___x_4046_;
v___y_4035_ = v___x_4051_;
goto v___jp_4033_;
}
}
}
v___jp_4003_:
{
lean_object* v___x_4006_; lean_object* v_toEnvExtension_4007_; uint8_t v_logWrites_4008_; 
v___x_4006_ = lean_st_ref_take(v___y_4005_);
v_toEnvExtension_4007_ = lean_ctor_get(v___x_3992_, 0);
v_logWrites_4008_ = lean_ctor_get_uint8(v_toEnvExtension_4007_, sizeof(void*)*6);
if (v_logWrites_4008_ == 0)
{
lean_object* v_env_4009_; lean_object* v_nextMacroScope_4010_; lean_object* v_ngen_4011_; lean_object* v_auxDeclNGen_4012_; lean_object* v_traceState_4013_; lean_object* v_recordedDeps_4014_; lean_object* v_messages_4015_; lean_object* v_infoState_4016_; lean_object* v_snapshotTasks_4017_; lean_object* v_asyncMode_4018_; lean_object* v___x_4019_; 
v_env_4009_ = lean_ctor_get(v___x_4006_, 0);
lean_inc_ref(v_env_4009_);
v_nextMacroScope_4010_ = lean_ctor_get(v___x_4006_, 1);
lean_inc(v_nextMacroScope_4010_);
v_ngen_4011_ = lean_ctor_get(v___x_4006_, 2);
lean_inc_ref(v_ngen_4011_);
v_auxDeclNGen_4012_ = lean_ctor_get(v___x_4006_, 3);
lean_inc_ref(v_auxDeclNGen_4012_);
v_traceState_4013_ = lean_ctor_get(v___x_4006_, 4);
lean_inc_ref(v_traceState_4013_);
v_recordedDeps_4014_ = lean_ctor_get(v___x_4006_, 6);
lean_inc_ref(v_recordedDeps_4014_);
v_messages_4015_ = lean_ctor_get(v___x_4006_, 7);
lean_inc_ref(v_messages_4015_);
v_infoState_4016_ = lean_ctor_get(v___x_4006_, 8);
lean_inc_ref(v_infoState_4016_);
v_snapshotTasks_4017_ = lean_ctor_get(v___x_4006_, 9);
lean_inc_ref(v_snapshotTasks_4017_);
lean_dec(v___x_4006_);
v_asyncMode_4018_ = lean_ctor_get(v_toEnvExtension_4007_, 2);
lean_inc_ref(v_toEnvExtension_4007_);
v___x_4019_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4007_, v_env_4009_, v___f_4001_, v_asyncMode_4018_, v___x_3994_, v___x_4002_);
v___y_3954_ = v___y_4005_;
v___y_3955_ = v_ngen_4011_;
v___y_3956_ = v_infoState_4016_;
v___y_3957_ = v_messages_4015_;
v___y_3958_ = v_nextMacroScope_4010_;
v___y_3959_ = v_recordedDeps_4014_;
v___y_3960_ = v_snapshotTasks_4017_;
v___y_3961_ = v_traceState_4013_;
v___y_3962_ = v___y_4004_;
v___y_3963_ = v_auxDeclNGen_4012_;
v___y_3964_ = v___x_4019_;
goto v___jp_3953_;
}
else
{
lean_object* v_env_4020_; lean_object* v_nextMacroScope_4021_; lean_object* v_ngen_4022_; lean_object* v_auxDeclNGen_4023_; lean_object* v_traceState_4024_; lean_object* v_recordedDeps_4025_; lean_object* v_messages_4026_; lean_object* v_infoState_4027_; lean_object* v_snapshotTasks_4028_; lean_object* v_asyncMode_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_env_4020_ = lean_ctor_get(v___x_4006_, 0);
lean_inc_ref(v_env_4020_);
v_nextMacroScope_4021_ = lean_ctor_get(v___x_4006_, 1);
lean_inc(v_nextMacroScope_4021_);
v_ngen_4022_ = lean_ctor_get(v___x_4006_, 2);
lean_inc_ref(v_ngen_4022_);
v_auxDeclNGen_4023_ = lean_ctor_get(v___x_4006_, 3);
lean_inc_ref(v_auxDeclNGen_4023_);
v_traceState_4024_ = lean_ctor_get(v___x_4006_, 4);
lean_inc_ref(v_traceState_4024_);
v_recordedDeps_4025_ = lean_ctor_get(v___x_4006_, 6);
lean_inc_ref(v_recordedDeps_4025_);
v_messages_4026_ = lean_ctor_get(v___x_4006_, 7);
lean_inc_ref(v_messages_4026_);
v_infoState_4027_ = lean_ctor_get(v___x_4006_, 8);
lean_inc_ref(v_infoState_4027_);
v_snapshotTasks_4028_ = lean_ctor_get(v___x_4006_, 9);
lean_inc_ref(v_snapshotTasks_4028_);
lean_dec(v___x_4006_);
v_asyncMode_4029_ = lean_ctor_get(v_toEnvExtension_4007_, 2);
lean_inc_ref_n(v_toEnvExtension_4007_, 2);
v___x_4030_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4007_, v_env_4020_);
lean_dec_ref(v_env_4020_);
v___x_4031_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4007_, v___x_4030_, v___f_4001_, v_asyncMode_4029_, v___x_3994_, v___x_4002_);
v___y_3954_ = v___y_4005_;
v___y_3955_ = v_ngen_4022_;
v___y_3956_ = v_infoState_4027_;
v___y_3957_ = v_messages_4026_;
v___y_3958_ = v_nextMacroScope_4021_;
v___y_3959_ = v_recordedDeps_4025_;
v___y_3960_ = v_snapshotTasks_4028_;
v___y_3961_ = v_traceState_4024_;
v___y_3962_ = v___y_4004_;
v___y_3963_ = v_auxDeclNGen_4023_;
v___y_3964_ = v___x_4031_;
goto v___jp_3953_;
}
}
}
else
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
lean_dec_ref_known(v_entry_3989_, 1);
lean_dec(v_hint_3947_);
lean_dec(v_mod_3945_);
v___x_4065_ = lean_box(0);
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
return v___x_4066_;
}
v___jp_3953_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v_mctx_3969_; lean_object* v_zetaDeltaFVarIds_3970_; lean_object* v_postponed_3971_; lean_object* v_diag_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3983_; 
v___x_3965_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
v___x_3966_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3966_, 0, v___y_3964_);
lean_ctor_set(v___x_3966_, 1, v___y_3958_);
lean_ctor_set(v___x_3966_, 2, v___y_3955_);
lean_ctor_set(v___x_3966_, 3, v___y_3963_);
lean_ctor_set(v___x_3966_, 4, v___y_3961_);
lean_ctor_set(v___x_3966_, 5, v___x_3965_);
lean_ctor_set(v___x_3966_, 6, v___y_3959_);
lean_ctor_set(v___x_3966_, 7, v___y_3957_);
lean_ctor_set(v___x_3966_, 8, v___y_3956_);
lean_ctor_set(v___x_3966_, 9, v___y_3960_);
v___x_3967_ = lean_st_ref_put(v___y_3954_, v___x_3966_);
v___x_3968_ = lean_st_ref_take(v___y_3962_);
v_mctx_3969_ = lean_ctor_get(v___x_3968_, 0);
v_zetaDeltaFVarIds_3970_ = lean_ctor_get(v___x_3968_, 2);
v_postponed_3971_ = lean_ctor_get(v___x_3968_, 3);
v_diag_3972_ = lean_ctor_get(v___x_3968_, 4);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; 
v_unused_3984_ = lean_ctor_get(v___x_3968_, 1);
lean_dec(v_unused_3984_);
v___x_3974_ = v___x_3968_;
v_isShared_3975_ = v_isSharedCheck_3983_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_diag_3972_);
lean_inc(v_postponed_3971_);
lean_inc(v_zetaDeltaFVarIds_3970_);
lean_inc(v_mctx_3969_);
lean_dec(v___x_3968_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3983_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__3);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_3977_);
v___x_3979_ = v___x_3974_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_mctx_3969_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_zetaDeltaFVarIds_3970_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_postponed_3971_);
lean_ctor_set(v_reuseFailAlloc_3982_, 4, v_diag_3972_);
v___x_3979_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_st_ref_put(v___y_3962_, v___x_3979_);
v___x_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3976_);
return v___x_3981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___boxed(lean_object* v_mod_4067_, lean_object* v_isMeta_4068_, lean_object* v_hint_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
uint8_t v_isMeta_boxed_4075_; lean_object* v_res_4076_; 
v_isMeta_boxed_4075_ = lean_unbox(v_isMeta_4068_);
v_res_4076_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_mod_4067_, v_isMeta_boxed_4075_, v_hint_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(lean_object* v_a_4077_, lean_object* v_x_4078_){
_start:
{
if (lean_obj_tag(v_x_4078_) == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_box(0);
return v___x_4079_;
}
else
{
lean_object* v_key_4080_; lean_object* v_value_4081_; lean_object* v_tail_4082_; uint8_t v___x_4083_; 
v_key_4080_ = lean_ctor_get(v_x_4078_, 0);
v_value_4081_ = lean_ctor_get(v_x_4078_, 1);
v_tail_4082_ = lean_ctor_get(v_x_4078_, 2);
v___x_4083_ = lean_name_eq(v_key_4080_, v_a_4077_);
if (v___x_4083_ == 0)
{
v_x_4078_ = v_tail_4082_;
goto _start;
}
else
{
lean_object* v___x_4085_; 
lean_inc(v_value_4081_);
v___x_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4085_, 0, v_value_4081_);
return v___x_4085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_a_4086_, lean_object* v_x_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4086_, v_x_4087_);
lean_dec(v_x_4087_);
lean_dec(v_a_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(lean_object* v_m_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v_buckets_4091_; lean_object* v___x_4092_; uint64_t v___y_4094_; 
v_buckets_4091_ = lean_ctor_get(v_m_4089_, 1);
v___x_4092_ = lean_array_get_size(v_buckets_4091_);
if (lean_obj_tag(v_a_4090_) == 0)
{
uint64_t v___x_4108_; 
v___x_4108_ = 1723ULL;
v___y_4094_ = v___x_4108_;
goto v___jp_4093_;
}
else
{
uint64_t v_hash_4109_; 
v_hash_4109_ = lean_ctor_get_uint64(v_a_4090_, sizeof(void*)*2);
v___y_4094_ = v_hash_4109_;
goto v___jp_4093_;
}
v___jp_4093_:
{
uint64_t v___x_4095_; uint64_t v___x_4096_; uint64_t v_fold_4097_; uint64_t v___x_4098_; uint64_t v___x_4099_; uint64_t v___x_4100_; size_t v___x_4101_; size_t v___x_4102_; size_t v___x_4103_; size_t v___x_4104_; size_t v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4095_ = 32ULL;
v___x_4096_ = lean_uint64_shift_right(v___y_4094_, v___x_4095_);
v_fold_4097_ = lean_uint64_xor(v___y_4094_, v___x_4096_);
v___x_4098_ = 16ULL;
v___x_4099_ = lean_uint64_shift_right(v_fold_4097_, v___x_4098_);
v___x_4100_ = lean_uint64_xor(v_fold_4097_, v___x_4099_);
v___x_4101_ = lean_uint64_to_usize(v___x_4100_);
v___x_4102_ = lean_usize_of_nat(v___x_4092_);
v___x_4103_ = ((size_t)1ULL);
v___x_4104_ = lean_usize_sub(v___x_4102_, v___x_4103_);
v___x_4105_ = lean_usize_land(v___x_4101_, v___x_4104_);
v___x_4106_ = lean_array_uget_borrowed(v_buckets_4091_, v___x_4105_);
v___x_4107_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4090_, v___x_4106_);
return v___x_4107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg___boxed(lean_object* v_m_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4110_, v_a_4111_);
lean_dec(v_a_4111_);
lean_dec_ref(v_m_4110_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v___x_4113_, lean_object* v_declName_4114_, lean_object* v_as_4115_, size_t v_sz_4116_, size_t v_i_4117_, lean_object* v_b_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
uint8_t v___x_4124_; 
v___x_4124_ = lean_usize_dec_lt(v_i_4117_, v_sz_4116_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; 
lean_dec(v_declName_4114_);
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_b_4118_);
return v___x_4125_;
}
else
{
lean_object* v___x_4126_; lean_object* v_modules_4127_; lean_object* v___x_4128_; lean_object* v_a_4129_; lean_object* v___x_4130_; lean_object* v_toImport_4131_; lean_object* v_module_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; lean_object* v___x_4135_; 
v___x_4126_ = l_Lean_Environment_header(v___x_4113_);
v_modules_4127_ = lean_ctor_get(v___x_4126_, 3);
lean_inc_ref(v_modules_4127_);
lean_dec_ref(v___x_4126_);
v___x_4128_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4129_ = lean_array_uget_borrowed(v_as_4115_, v_i_4117_);
v___x_4130_ = lean_array_get(v___x_4128_, v_modules_4127_, v_a_4129_);
lean_dec_ref(v_modules_4127_);
v_toImport_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc_ref(v_toImport_4131_);
lean_dec(v___x_4130_);
v_module_4132_ = lean_ctor_get(v_toImport_4131_, 0);
lean_inc(v_module_4132_);
lean_dec_ref(v_toImport_4131_);
v___x_4133_ = lean_box(0);
v___x_4134_ = 0;
lean_inc(v_declName_4114_);
v___x_4135_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4132_, v___x_4134_, v_declName_4114_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
if (lean_obj_tag(v___x_4135_) == 0)
{
size_t v___x_4136_; size_t v___x_4137_; 
lean_dec_ref_known(v___x_4135_, 1);
v___x_4136_ = ((size_t)1ULL);
v___x_4137_ = lean_usize_add(v_i_4117_, v___x_4136_);
v_i_4117_ = v___x_4137_;
v_b_4118_ = v___x_4133_;
goto _start;
}
else
{
lean_dec(v_declName_4114_);
return v___x_4135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v___x_4139_, lean_object* v_declName_4140_, lean_object* v_as_4141_, lean_object* v_sz_4142_, lean_object* v_i_4143_, lean_object* v_b_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
size_t v_sz_boxed_4150_; size_t v_i_boxed_4151_; lean_object* v_res_4152_; 
v_sz_boxed_4150_ = lean_unbox_usize(v_sz_4142_);
lean_dec(v_sz_4142_);
v_i_boxed_4151_ = lean_unbox_usize(v_i_4143_);
lean_dec(v_i_4143_);
v_res_4152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v___x_4139_, v_declName_4140_, v_as_4141_, v_sz_boxed_4150_, v_i_boxed_4151_, v_b_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec_ref(v_as_4141_);
lean_dec_ref(v___x_4139_);
return v_res_4152_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Std_HashMap_instInhabited___redArg();
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_4156_, uint8_t v_isMeta_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v_env_4168_; lean_object* v___y_4170_; lean_object* v___x_4183_; 
v___x_4163_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4164_ = lean_st_ref_get(v___y_4161_);
v_env_4168_ = lean_ctor_get(v___x_4164_, 0);
lean_inc_ref(v_env_4168_);
lean_dec(v___x_4164_);
v___x_4183_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4168_, v_declName_4156_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_dec_ref(v_env_4168_);
lean_dec(v_declName_4156_);
goto v___jp_4165_;
}
else
{
lean_object* v_val_4184_; lean_object* v___x_4185_; lean_object* v_modules_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_val_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_val_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = l_Lean_Environment_header(v_env_4168_);
v_modules_4186_ = lean_ctor_get(v___x_4185_, 3);
lean_inc_ref(v_modules_4186_);
lean_dec_ref(v___x_4185_);
v___x_4187_ = lean_array_get_size(v_modules_4186_);
v___x_4188_ = lean_nat_dec_lt(v_val_4184_, v___x_4187_);
if (v___x_4188_ == 0)
{
lean_dec_ref(v_modules_4186_);
lean_dec(v_val_4184_);
lean_dec_ref(v_env_4168_);
lean_dec(v_declName_4156_);
goto v___jp_4165_;
}
else
{
lean_object* v___x_4189_; lean_object* v___x_4190_; uint8_t v___y_4192_; 
v___x_4189_ = lean_array_fget(v_modules_4186_, v_val_4184_);
lean_dec(v_val_4184_);
lean_dec_ref(v_modules_4186_);
v___x_4190_ = lean_st_ref_get(v___y_4161_);
if (v_isMeta_4157_ == 0)
{
lean_dec(v___x_4190_);
v___y_4192_ = v_isMeta_4157_;
goto v___jp_4191_;
}
else
{
lean_object* v_env_4203_; uint8_t v___x_4204_; 
v_env_4203_ = lean_ctor_get(v___x_4190_, 0);
lean_inc_ref(v_env_4203_);
lean_dec(v___x_4190_);
lean_inc(v_declName_4156_);
v___x_4204_ = l_Lean_isMarkedMeta(v_env_4203_, v_declName_4156_);
if (v___x_4204_ == 0)
{
v___y_4192_ = v_isMeta_4157_;
goto v___jp_4191_;
}
else
{
uint8_t v___x_4205_; 
v___x_4205_ = 0;
v___y_4192_ = v___x_4205_;
goto v___jp_4191_;
}
}
v___jp_4191_:
{
lean_object* v_toImport_4193_; lean_object* v_module_4194_; lean_object* v___x_4195_; 
v_toImport_4193_ = lean_ctor_get(v___x_4189_, 0);
lean_inc_ref(v_toImport_4193_);
lean_dec(v___x_4189_);
v_module_4194_ = lean_ctor_get(v_toImport_4193_, 0);
lean_inc(v_module_4194_);
lean_dec_ref(v_toImport_4193_);
lean_inc(v_declName_4156_);
v___x_4195_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2(v_module_4194_, v___y_4192_, v_declName_4156_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_dec_ref_known(v___x_4195_, 1);
v___x_4196_ = l_Lean_indirectModUseExt;
v___x_4197_ = lean_box(1);
v___x_4198_ = lean_box(0);
lean_inc_ref(v_env_4168_);
v___x_4199_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4163_, v___x_4196_, v_env_4168_, v___x_4197_, v___x_4198_);
v___x_4200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4199_, v_declName_4156_);
lean_dec(v___x_4199_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v___x_4201_; 
v___x_4201_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4170_ = v___x_4201_;
goto v___jp_4169_;
}
else
{
lean_object* v_val_4202_; 
v_val_4202_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_val_4202_);
lean_dec_ref_known(v___x_4200_, 1);
v___y_4170_ = v_val_4202_;
goto v___jp_4169_;
}
}
else
{
lean_dec_ref(v_env_4168_);
lean_dec(v_declName_4156_);
return v___x_4195_;
}
}
}
}
v___jp_4165_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_box(0);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
v___jp_4169_:
{
lean_object* v___x_4171_; size_t v_sz_4172_; size_t v___x_4173_; lean_object* v___x_4174_; 
v___x_4171_ = lean_box(0);
v_sz_4172_ = lean_array_size(v___y_4170_);
v___x_4173_ = ((size_t)0ULL);
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_env_4168_, v_declName_4156_, v___y_4170_, v_sz_4172_, v___x_4173_, v___x_4171_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec_ref(v___y_4170_);
lean_dec_ref(v_env_4168_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; 
v_unused_4182_ = lean_ctor_get(v___x_4174_, 0);
lean_dec(v_unused_4182_);
v___x_4176_ = v___x_4174_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_dec(v___x_4174_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4171_);
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4171_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
else
{
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_4206_, lean_object* v_isMeta_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
uint8_t v_isMeta_boxed_4213_; lean_object* v_res_4214_; 
v_isMeta_boxed_4213_ = lean_unbox(v_isMeta_4207_);
v_res_4214_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4206_, v_isMeta_boxed_4213_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_4215_, uint8_t v_when_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
if (v_when_4216_ == 0)
{
lean_object* v___x_4222_; 
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
lean_inc(v___y_4218_);
lean_inc_ref(v___y_4217_);
v___x_4222_ = lean_apply_5(v_x_4215_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, lean_box(0));
return v___x_4222_;
}
else
{
uint8_t v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = 0;
v___x_4224_ = l_Lean_withExporting___at___00Lean_Meta_Grind_addNormTheorem_spec__0___redArg(v_x_4215_, v___x_4223_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
return v___x_4224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_4225_, lean_object* v_when_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
uint8_t v_when_boxed_4232_; lean_object* v_res_4233_; 
v_when_boxed_4232_ = lean_unbox(v_when_4226_);
v_res_4233_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4225_, v_when_boxed_4232_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_4234_, uint8_t v_showInfo_4235_, uint8_t v_minIndexable_4236_, lean_object* v_attrName_4237_, lean_object* v___x_4238_, lean_object* v_declName_4239_, lean_object* v_stx_4240_, uint8_t v_attrKind_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
uint8_t v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___f_4250_; uint8_t v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4245_ = 0;
v___x_4246_ = lean_box(v_attrKind_4241_);
v___x_4247_ = lean_box(v_showInfo_4235_);
v___x_4248_ = lean_box(v_minIndexable_4236_);
v___x_4249_ = lean_box(v___x_4245_);
lean_inc(v_declName_4239_);
v___f_4250_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_4250_, 0, v_declName_4239_);
lean_closure_set(v___f_4250_, 1, v___x_4246_);
lean_closure_set(v___f_4250_, 2, v_stx_4240_);
lean_closure_set(v___f_4250_, 3, v_ext_4234_);
lean_closure_set(v___f_4250_, 4, v___x_4247_);
lean_closure_set(v___f_4250_, 5, v___x_4248_);
lean_closure_set(v___f_4250_, 6, v___x_4249_);
lean_closure_set(v___f_4250_, 7, v_attrName_4237_);
v___x_4251_ = 1;
v___x_4252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_4253_ = lean_unsigned_to_nat(32u);
v___x_4254_ = lean_mk_empty_array_with_capacity(v___x_4253_);
lean_dec_ref(v___x_4254_);
v___x_4255_ = lean_unsigned_to_nat(0u);
v___x_4256_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_4257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_4258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_4259_ = lean_box(0);
lean_inc(v___x_4238_);
v___x_4260_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4260_, 0, v___x_4252_);
lean_ctor_set(v___x_4260_, 1, v___x_4238_);
lean_ctor_set(v___x_4260_, 2, v___x_4257_);
lean_ctor_set(v___x_4260_, 3, v___x_4258_);
lean_ctor_set(v___x_4260_, 4, v___x_4259_);
lean_ctor_set(v___x_4260_, 5, v___x_4255_);
lean_ctor_set(v___x_4260_, 6, v___x_4259_);
lean_ctor_set_uint8(v___x_4260_, sizeof(void*)*7, v___x_4245_);
lean_ctor_set_uint8(v___x_4260_, sizeof(void*)*7 + 1, v___x_4245_);
lean_ctor_set_uint8(v___x_4260_, sizeof(void*)*7 + 2, v___x_4245_);
lean_ctor_set_uint8(v___x_4260_, sizeof(void*)*7 + 3, v___x_4251_);
v___x_4261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_4262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_4263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_4264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4261_);
lean_ctor_set(v___x_4264_, 1, v___x_4262_);
lean_ctor_set(v___x_4264_, 2, v___x_4238_);
lean_ctor_set(v___x_4264_, 3, v___x_4256_);
lean_ctor_set(v___x_4264_, 4, v___x_4263_);
v___x_4265_ = lean_st_mk_ref(v___x_4264_);
v___x_4266_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_4239_, v___x_4245_, v___x_4260_, v___x_4265_, v___y_4242_, v___y_4243_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v___x_4267_; 
lean_dec_ref_known(v___x_4266_, 1);
v___x_4267_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_4250_, v___x_4251_, v___x_4260_, v___x_4265_, v___y_4242_, v___y_4243_);
lean_dec_ref_known(v___x_4260_, 7);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4276_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4270_ = v___x_4267_;
v_isShared_4271_ = v_isSharedCheck_4276_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4267_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4276_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4272_ = lean_st_ref_get(v___x_4265_);
lean_dec(v___x_4265_);
lean_dec(v___x_4272_);
if (v_isShared_4271_ == 0)
{
v___x_4274_ = v___x_4270_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4268_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
else
{
lean_dec(v___x_4265_);
return v___x_4267_;
}
}
else
{
lean_dec(v___x_4265_);
lean_dec_ref_known(v___x_4260_, 7);
lean_dec_ref(v___f_4250_);
return v___x_4266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_4277_, lean_object* v_showInfo_4278_, lean_object* v_minIndexable_4279_, lean_object* v_attrName_4280_, lean_object* v___x_4281_, lean_object* v_declName_4282_, lean_object* v_stx_4283_, lean_object* v_attrKind_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
uint8_t v_showInfo_boxed_4288_; uint8_t v_minIndexable_boxed_4289_; uint8_t v_attrKind_boxed_4290_; lean_object* v_res_4291_; 
v_showInfo_boxed_4288_ = lean_unbox(v_showInfo_4278_);
v_minIndexable_boxed_4289_ = lean_unbox(v_minIndexable_4279_);
v_attrKind_boxed_4290_ = lean_unbox(v_attrKind_4284_);
v_res_4291_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_4277_, v_showInfo_boxed_4288_, v_minIndexable_boxed_4289_, v_attrName_4280_, v___x_4281_, v_declName_4282_, v_stx_4283_, v_attrKind_boxed_4290_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_4314_, uint8_t v_minIndexable_4315_, uint8_t v_showInfo_4316_, lean_object* v_ext_4317_, lean_object* v_ref_4318_){
_start:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___f_4325_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4371_; 
v___x_4320_ = lean_box(1);
v___x_4321_ = lean_box(v_showInfo_4316_);
lean_inc_n(v_attrName_4314_, 2);
lean_inc_ref(v_ext_4317_);
v___f_4322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4322_, 0, v_ext_4317_);
lean_closure_set(v___f_4322_, 1, v___x_4320_);
lean_closure_set(v___f_4322_, 2, v___x_4321_);
lean_closure_set(v___f_4322_, 3, v_attrName_4314_);
v___x_4323_ = lean_box(v_showInfo_4316_);
v___x_4324_ = lean_box(v_minIndexable_4315_);
v___f_4325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_4325_, 0, v_ext_4317_);
lean_closure_set(v___f_4325_, 1, v___x_4323_);
lean_closure_set(v___f_4325_, 2, v___x_4324_);
lean_closure_set(v___f_4325_, 3, v_attrName_4314_);
lean_closure_set(v___f_4325_, 4, v___x_4320_);
if (v_minIndexable_4315_ == 0)
{
if (v_showInfo_4316_ == 0)
{
lean_inc(v_attrName_4314_);
v___y_4371_ = v_attrName_4314_;
goto v___jp_4370_;
}
else
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_4314_);
v___x_4400_ = lean_name_append_after(v_attrName_4314_, v___x_4399_);
v___y_4371_ = v___x_4400_;
goto v___jp_4370_;
}
}
else
{
if (v_showInfo_4316_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_4314_);
v___x_4402_ = lean_name_append_after(v_attrName_4314_, v___x_4401_);
v___y_4371_ = v___x_4402_;
goto v___jp_4370_;
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_4314_);
v___x_4404_ = lean_name_append_after(v_attrName_4314_, v___x_4403_);
v___y_4371_ = v___x_4404_;
goto v___jp_4370_;
}
}
v___jp_4326_:
{
lean_object* v___x_4329_; uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_4330_ = 1;
v___x_4331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4314_, v___x_4330_);
v___x_4332_ = lean_string_append(v___x_4329_, v___x_4331_);
v___x_4333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_4334_ = lean_string_append(v___x_4332_, v___x_4333_);
v___x_4335_ = lean_string_append(v___x_4334_, v___x_4331_);
v___x_4336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_4337_ = lean_string_append(v___x_4335_, v___x_4336_);
v___x_4338_ = lean_string_append(v___x_4337_, v___x_4331_);
v___x_4339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_4340_ = lean_string_append(v___x_4338_, v___x_4339_);
v___x_4341_ = lean_string_append(v___x_4340_, v___x_4331_);
v___x_4342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_4343_ = lean_string_append(v___x_4341_, v___x_4342_);
v___x_4344_ = lean_string_append(v___x_4343_, v___x_4331_);
v___x_4345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_4346_ = lean_string_append(v___x_4344_, v___x_4345_);
v___x_4347_ = lean_string_append(v___x_4346_, v___x_4331_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_4349_ = lean_string_append(v___x_4347_, v___x_4348_);
v___x_4350_ = lean_string_append(v___x_4349_, v___x_4331_);
v___x_4351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_4352_ = lean_string_append(v___x_4350_, v___x_4351_);
v___x_4353_ = lean_string_append(v___x_4352_, v___x_4331_);
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_4355_ = lean_string_append(v___x_4353_, v___x_4354_);
v___x_4356_ = lean_string_append(v___x_4355_, v___x_4331_);
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_4358_ = lean_string_append(v___x_4356_, v___x_4357_);
v___x_4359_ = lean_string_append(v___x_4358_, v___x_4331_);
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_4361_ = lean_string_append(v___x_4359_, v___x_4360_);
v___x_4362_ = lean_string_append(v___x_4361_, v___x_4331_);
lean_dec_ref(v___x_4331_);
v___x_4363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_4364_ = lean_string_append(v___x_4362_, v___x_4363_);
v___x_4365_ = lean_string_append(v___y_4328_, v___x_4364_);
lean_dec_ref(v___x_4364_);
v___x_4366_ = 1;
v___x_4367_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4367_, 0, v_ref_4318_);
lean_ctor_set(v___x_4367_, 1, v___y_4327_);
lean_ctor_set(v___x_4367_, 2, v___x_4365_);
lean_ctor_set_uint8(v___x_4367_, sizeof(void*)*3, v___x_4366_);
v___x_4368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
lean_ctor_set(v___x_4368_, 1, v___f_4325_);
lean_ctor_set(v___x_4368_, 2, v___f_4322_);
v___x_4369_ = l_Lean_registerBuiltinAttribute(v___x_4368_);
return v___x_4369_;
}
v___jp_4370_:
{
if (v_minIndexable_4315_ == 0)
{
if (v_showInfo_4316_ == 0)
{
lean_object* v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_4373_ = 1;
lean_inc(v_attrName_4314_);
v___x_4374_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4314_, v___x_4373_);
v___x_4375_ = lean_string_append(v___x_4372_, v___x_4374_);
lean_dec_ref(v___x_4374_);
v___x_4376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_4377_ = lean_string_append(v___x_4375_, v___x_4376_);
v___y_4327_ = v___y_4371_;
v___y_4328_ = v___x_4377_;
goto v___jp_4326_;
}
else
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4314_);
v___x_4379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4314_, v_showInfo_4316_);
v___x_4380_ = lean_string_append(v___x_4378_, v___x_4379_);
v___x_4381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_4382_ = lean_string_append(v___x_4380_, v___x_4381_);
v___x_4383_ = lean_string_append(v___x_4382_, v___x_4379_);
lean_dec_ref(v___x_4379_);
v___x_4384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_4385_ = lean_string_append(v___x_4383_, v___x_4384_);
v___y_4327_ = v___y_4371_;
v___y_4328_ = v___x_4385_;
goto v___jp_4326_;
}
}
else
{
if (v_showInfo_4316_ == 0)
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4314_);
v___x_4387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4314_, v_minIndexable_4315_);
v___x_4388_ = lean_string_append(v___x_4386_, v___x_4387_);
lean_dec_ref(v___x_4387_);
v___x_4389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_4390_ = lean_string_append(v___x_4388_, v___x_4389_);
v___y_4327_ = v___y_4371_;
v___y_4328_ = v___x_4390_;
goto v___jp_4326_;
}
else
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_4314_);
v___x_4392_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4314_, v_showInfo_4316_);
v___x_4393_ = lean_string_append(v___x_4391_, v___x_4392_);
v___x_4394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_4395_ = lean_string_append(v___x_4393_, v___x_4394_);
v___x_4396_ = lean_string_append(v___x_4395_, v___x_4392_);
lean_dec_ref(v___x_4392_);
v___x_4397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_4398_ = lean_string_append(v___x_4396_, v___x_4397_);
v___y_4327_ = v___y_4371_;
v___y_4328_ = v___x_4398_;
goto v___jp_4326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_4405_, lean_object* v_minIndexable_4406_, lean_object* v_showInfo_4407_, lean_object* v_ext_4408_, lean_object* v_ref_4409_, lean_object* v_a_4410_){
_start:
{
uint8_t v_minIndexable_boxed_4411_; uint8_t v_showInfo_boxed_4412_; lean_object* v_res_4413_; 
v_minIndexable_boxed_4411_ = lean_unbox(v_minIndexable_4406_);
v_showInfo_boxed_4412_ = lean_unbox(v_showInfo_4407_);
v_res_4413_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4405_, v_minIndexable_boxed_4411_, v_showInfo_boxed_4412_, v_ext_4408_, v_ref_4409_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_4414_, lean_object* v_msg_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_4422_, lean_object* v_msg_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_4422_, v_msg_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_4430_, uint8_t v_attrKind_4431_, uint8_t v_showInfo_4432_, uint8_t v_minIndexable_4433_, lean_object* v_as_4434_, lean_object* v_as_x27_4435_, lean_object* v_b_4436_, lean_object* v_a_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_4430_, v_attrKind_4431_, v_showInfo_4432_, v_minIndexable_4433_, v_as_x27_4435_, v_b_4436_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_4444_, lean_object* v_attrKind_4445_, lean_object* v_showInfo_4446_, lean_object* v_minIndexable_4447_, lean_object* v_as_4448_, lean_object* v_as_x27_4449_, lean_object* v_b_4450_, lean_object* v_a_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
uint8_t v_attrKind_boxed_4457_; uint8_t v_showInfo_boxed_4458_; uint8_t v_minIndexable_boxed_4459_; lean_object* v_res_4460_; 
v_attrKind_boxed_4457_ = lean_unbox(v_attrKind_4445_);
v_showInfo_boxed_4458_ = lean_unbox(v_showInfo_4446_);
v_minIndexable_boxed_4459_ = lean_unbox(v_minIndexable_4447_);
v_res_4460_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_4444_, v_attrKind_boxed_4457_, v_showInfo_boxed_4458_, v_minIndexable_boxed_4459_, v_as_4448_, v_as_x27_4449_, v_b_4450_, v_a_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v_as_x27_4449_);
lean_dec(v_as_4448_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_4461_, lean_object* v_x_4462_, uint8_t v_when_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_4462_, v_when_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_4470_, lean_object* v_x_4471_, lean_object* v_when_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
uint8_t v_when_boxed_4478_; lean_object* v_res_4479_; 
v_when_boxed_4478_ = lean_unbox(v_when_4472_);
v_res_4479_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_4470_, v_x_4471_, v_when_boxed_4478_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v_00_u03b2_4480_, lean_object* v_m_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v_m_4481_, v_a_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_4484_, lean_object* v_m_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_00_u03b2_4484_, v_m_4485_, v_a_4486_);
lean_dec(v_a_4486_);
lean_dec_ref(v_m_4485_);
return v_res_4487_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_4488_, lean_object* v_x_4489_, lean_object* v_x_4490_){
_start:
{
uint8_t v___x_4491_; 
v___x_4491_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v_x_4489_, v_x_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4492_, lean_object* v_x_4493_, lean_object* v_x_4494_){
_start:
{
uint8_t v_res_4495_; lean_object* v_r_4496_; 
v_res_4495_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3(v_00_u03b2_4492_, v_x_4493_, v_x_4494_);
lean_dec_ref(v_x_4494_);
lean_dec_ref(v_x_4493_);
v_r_4496_ = lean_box(v_res_4495_);
return v_r_4496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4497_, lean_object* v_a_4498_, lean_object* v_x_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___redArg(v_a_4498_, v_x_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4501_, lean_object* v_a_4502_, lean_object* v_x_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4_spec__6(v_00_u03b2_4501_, v_a_4502_, v_x_4503_);
lean_dec(v_x_4503_);
lean_dec(v_a_4502_);
return v_res_4504_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4505_, lean_object* v_x_4506_, size_t v_x_4507_, lean_object* v_x_4508_){
_start:
{
uint8_t v___x_4509_; 
v___x_4509_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___redArg(v_x_4506_, v_x_4507_, v_x_4508_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4510_, lean_object* v_x_4511_, lean_object* v_x_4512_, lean_object* v_x_4513_){
_start:
{
size_t v_x_12897__boxed_4514_; uint8_t v_res_4515_; lean_object* v_r_4516_; 
v_x_12897__boxed_4514_ = lean_unbox_usize(v_x_4512_);
lean_dec(v_x_4512_);
v_res_4515_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5(v_00_u03b2_4510_, v_x_4511_, v_x_12897__boxed_4514_, v_x_4513_);
lean_dec_ref(v_x_4513_);
lean_dec_ref(v_x_4511_);
v_r_4516_ = lean_box(v_res_4515_);
return v_r_4516_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4517_, lean_object* v_keys_4518_, lean_object* v_vals_4519_, lean_object* v_heq_4520_, lean_object* v_i_4521_, lean_object* v_k_4522_){
_start:
{
uint8_t v___x_4523_; 
v___x_4523_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___redArg(v_keys_4518_, v_i_4521_, v_k_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_4524_, lean_object* v_keys_4525_, lean_object* v_vals_4526_, lean_object* v_heq_4527_, lean_object* v_i_4528_, lean_object* v_k_4529_){
_start:
{
uint8_t v_res_4530_; lean_object* v_r_4531_; 
v_res_4530_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3_spec__5_spec__8(v_00_u03b2_4524_, v_keys_4525_, v_vals_4526_, v_heq_4527_, v_i_4528_, v_k_4529_);
lean_dec_ref(v_k_4529_);
lean_dec_ref(v_vals_4526_);
lean_dec_ref(v_keys_4525_);
v_r_4531_ = lean_box(v_res_4530_);
return v_r_4531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = lean_box(0);
v___x_4533_ = lean_unsigned_to_nat(16u);
v___x_4534_ = lean_mk_array(v___x_4533_, v___x_4532_);
return v___x_4534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4536_ = lean_unsigned_to_nat(0u);
v___x_4537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
lean_ctor_set(v___x_4537_, 1, v___x_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_4540_ = lean_st_mk_ref(v___x_4539_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_4544_, lean_object* v_msg_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v_ref_4549_; lean_object* v___x_4550_; lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4596_; 
v_ref_4549_ = lean_ctor_get(v___y_4546_, 2);
v___x_4550_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_4545_, v___y_4546_, v___y_4547_);
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4553_ = v___x_4550_;
v_isShared_4554_ = v_isSharedCheck_4596_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4550_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4596_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4555_; lean_object* v_traceState_4556_; lean_object* v_env_4557_; lean_object* v_nextMacroScope_4558_; lean_object* v_ngen_4559_; lean_object* v_auxDeclNGen_4560_; lean_object* v_cache_4561_; lean_object* v_recordedDeps_4562_; lean_object* v_messages_4563_; lean_object* v_infoState_4564_; lean_object* v_snapshotTasks_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4595_; 
v___x_4555_ = lean_st_ref_take(v___y_4547_);
v_traceState_4556_ = lean_ctor_get(v___x_4555_, 4);
v_env_4557_ = lean_ctor_get(v___x_4555_, 0);
v_nextMacroScope_4558_ = lean_ctor_get(v___x_4555_, 1);
v_ngen_4559_ = lean_ctor_get(v___x_4555_, 2);
v_auxDeclNGen_4560_ = lean_ctor_get(v___x_4555_, 3);
v_cache_4561_ = lean_ctor_get(v___x_4555_, 5);
v_recordedDeps_4562_ = lean_ctor_get(v___x_4555_, 6);
v_messages_4563_ = lean_ctor_get(v___x_4555_, 7);
v_infoState_4564_ = lean_ctor_get(v___x_4555_, 8);
v_snapshotTasks_4565_ = lean_ctor_get(v___x_4555_, 9);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4567_ = v___x_4555_;
v_isShared_4568_ = v_isSharedCheck_4595_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_snapshotTasks_4565_);
lean_inc(v_infoState_4564_);
lean_inc(v_messages_4563_);
lean_inc(v_recordedDeps_4562_);
lean_inc(v_cache_4561_);
lean_inc(v_traceState_4556_);
lean_inc(v_auxDeclNGen_4560_);
lean_inc(v_ngen_4559_);
lean_inc(v_nextMacroScope_4558_);
lean_inc(v_env_4557_);
lean_dec(v___x_4555_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4595_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
uint64_t v_tid_4569_; lean_object* v_traces_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4594_; 
v_tid_4569_ = lean_ctor_get_uint64(v_traceState_4556_, sizeof(void*)*1);
v_traces_4570_ = lean_ctor_get(v_traceState_4556_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_traceState_4556_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4572_ = v_traceState_4556_;
v_isShared_4573_ = v_isSharedCheck_4594_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_traces_4570_);
lean_dec(v_traceState_4556_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4594_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; double v___x_4576_; uint8_t v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4574_ = lean_box(0);
v___x_4575_ = lean_box(0);
v___x_4576_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__0);
v___x_4577_ = 0;
v___x_4578_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__1));
v___x_4579_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4579_, 0, v_cls_4544_);
lean_ctor_set(v___x_4579_, 1, v___x_4575_);
lean_ctor_set(v___x_4579_, 2, v___x_4578_);
lean_ctor_set_float(v___x_4579_, sizeof(void*)*3, v___x_4576_);
lean_ctor_set_float(v___x_4579_, sizeof(void*)*3 + 8, v___x_4576_);
lean_ctor_set_uint8(v___x_4579_, sizeof(void*)*3 + 16, v___x_4577_);
v___x_4580_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkNormSymTheorem_x3f_spec__0___closed__2));
v___x_4581_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4579_);
lean_ctor_set(v___x_4581_, 1, v_a_4551_);
lean_ctor_set(v___x_4581_, 2, v___x_4580_);
lean_inc(v_ref_4549_);
v___x_4582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4582_, 0, v_ref_4549_);
lean_ctor_set(v___x_4582_, 1, v___x_4581_);
v___x_4583_ = l_Lean_PersistentArray_push___redArg(v_traces_4570_, v___x_4582_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 0, v___x_4583_);
v___x_4585_ = v___x_4572_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4583_);
lean_ctor_set_uint64(v_reuseFailAlloc_4593_, sizeof(void*)*1, v_tid_4569_);
v___x_4585_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4587_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v___x_4585_);
v___x_4587_ = v___x_4567_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_env_4557_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_nextMacroScope_4558_);
lean_ctor_set(v_reuseFailAlloc_4592_, 2, v_ngen_4559_);
lean_ctor_set(v_reuseFailAlloc_4592_, 3, v_auxDeclNGen_4560_);
lean_ctor_set(v_reuseFailAlloc_4592_, 4, v___x_4585_);
lean_ctor_set(v_reuseFailAlloc_4592_, 5, v_cache_4561_);
lean_ctor_set(v_reuseFailAlloc_4592_, 6, v_recordedDeps_4562_);
lean_ctor_set(v_reuseFailAlloc_4592_, 7, v_messages_4563_);
lean_ctor_set(v_reuseFailAlloc_4592_, 8, v_infoState_4564_);
lean_ctor_set(v_reuseFailAlloc_4592_, 9, v_snapshotTasks_4565_);
v___x_4587_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; lean_object* v___x_4590_; 
v___x_4588_ = lean_st_ref_put(v___y_4547_, v___x_4587_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4574_);
v___x_4590_ = v___x_4553_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4574_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_4597_, lean_object* v_msg_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4597_, v_msg_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_4603_, uint8_t v_isMeta_4604_, lean_object* v_hint_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v_env_4627_; uint8_t v_isExporting_4628_; lean_object* v_entry_4629_; lean_object* v___x_4630_; lean_object* v_env_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___x_4625_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__0);
v___x_4626_ = lean_st_ref_get(v___y_4607_);
v_env_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc_ref(v_env_4627_);
lean_dec(v___x_4626_);
v_isExporting_4628_ = lean_ctor_get_uint8(v_env_4627_, sizeof(void*)*13);
lean_dec_ref(v_env_4627_);
lean_inc(v_mod_4603_);
v_entry_4629_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4629_, 0, v_mod_4603_);
lean_ctor_set_uint8(v_entry_4629_, sizeof(void*)*1, v_isExporting_4628_);
lean_ctor_set_uint8(v_entry_4629_, sizeof(void*)*1 + 1, v_isMeta_4604_);
v___x_4630_ = lean_st_ref_get(v___y_4607_);
v_env_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc_ref(v_env_4631_);
lean_dec(v___x_4630_);
v___x_4632_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4633_ = lean_box(1);
v___x_4634_ = lean_box(0);
v___x_4635_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4625_, v___x_4632_, v_env_4631_, v___x_4633_, v___x_4634_);
v___x_4636_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2_spec__3___redArg(v___x_4635_, v_entry_4629_);
lean_dec(v___x_4635_);
if (v___x_4636_ == 0)
{
lean_object* v_toCold_4637_; lean_object* v_options_4638_; lean_object* v_inheritedTraceOptions_4639_; uint8_t v_hasTrace_4640_; lean_object* v___f_4641_; uint8_t v___x_4642_; lean_object* v___y_4644_; 
v_toCold_4637_ = lean_ctor_get(v___y_4606_, 0);
v_options_4638_ = lean_ctor_get(v_toCold_4637_, 2);
v_inheritedTraceOptions_4639_ = lean_ctor_get(v_toCold_4637_, 11);
v_hasTrace_4640_ = lean_ctor_get_uint8(v_options_4638_, sizeof(void*)*1);
v___f_4641_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_4641_, 0, v___x_4632_);
lean_closure_set(v___f_4641_, 1, v_entry_4629_);
v___x_4642_ = 1;
if (v_hasTrace_4640_ == 0)
{
lean_dec(v_hint_4605_);
lean_dec(v_mod_4603_);
v___y_4644_ = v___y_4607_;
goto v___jp_4643_;
}
else
{
lean_object* v_cls_4662_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v_cls_4662_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__2));
v___x_4682_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__8);
v___x_4683_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4639_, v_options_4638_, v___x_4682_);
if (v___x_4683_ == 0)
{
lean_dec(v_hint_4605_);
lean_dec(v_mod_4603_);
v___y_4644_ = v___y_4607_;
goto v___jp_4643_;
}
else
{
lean_object* v___x_4684_; lean_object* v___y_4686_; 
v___x_4684_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__10);
if (v_isExporting_4628_ == 0)
{
lean_object* v___x_4693_; 
v___x_4693_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__15));
v___y_4686_ = v___x_4693_;
goto v___jp_4685_;
}
else
{
lean_object* v___x_4694_; 
v___x_4694_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__16));
v___y_4686_ = v___x_4694_;
goto v___jp_4685_;
}
v___jp_4685_:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_inc_ref(v___y_4686_);
v___x_4687_ = l_Lean_stringToMessageData(v___y_4686_);
v___x_4688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4684_);
lean_ctor_set(v___x_4688_, 1, v___x_4687_);
v___x_4689_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__12);
v___x_4690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4688_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
if (v_isMeta_4604_ == 0)
{
lean_object* v___x_4691_; 
v___x_4691_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__13));
v___y_4669_ = v___x_4690_;
v___y_4670_ = v___x_4691_;
goto v___jp_4668_;
}
else
{
lean_object* v___x_4692_; 
v___x_4692_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__14));
v___y_4669_ = v___x_4690_;
v___y_4670_ = v___x_4692_;
goto v___jp_4668_;
}
}
}
v___jp_4663_:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___y_4664_);
lean_ctor_set(v___x_4666_, 1, v___y_4665_);
v___x_4667_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_4662_, v___x_4666_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_dec_ref_known(v___x_4667_, 1);
v___y_4644_ = v___y_4607_;
goto v___jp_4643_;
}
else
{
lean_dec_ref(v___f_4641_);
return v___x_4667_;
}
}
v___jp_4668_:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; uint8_t v___x_4677_; 
lean_inc_ref(v___y_4670_);
v___x_4671_ = l_Lean_stringToMessageData(v___y_4670_);
v___x_4672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___y_4669_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
v___x_4673_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__4);
v___x_4674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4672_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
v___x_4675_ = l_Lean_MessageData_ofName(v_mod_4603_);
v___x_4676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4674_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
v___x_4677_ = l_Lean_Name_isAnonymous(v_hint_4605_);
if (v___x_4677_ == 0)
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4678_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__6);
v___x_4679_ = l_Lean_MessageData_ofName(v_hint_4605_);
v___x_4680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4678_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
v___y_4664_ = v___x_4676_;
v___y_4665_ = v___x_4680_;
goto v___jp_4663_;
}
else
{
lean_object* v___x_4681_; 
lean_dec(v_hint_4605_);
v___x_4681_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__2___closed__7);
v___y_4664_ = v___x_4676_;
v___y_4665_ = v___x_4681_;
goto v___jp_4663_;
}
}
}
v___jp_4643_:
{
lean_object* v___x_4645_; lean_object* v_toEnvExtension_4646_; lean_object* v_env_4647_; lean_object* v_nextMacroScope_4648_; lean_object* v_ngen_4649_; lean_object* v_auxDeclNGen_4650_; lean_object* v_traceState_4651_; lean_object* v_recordedDeps_4652_; lean_object* v_messages_4653_; lean_object* v_infoState_4654_; lean_object* v_snapshotTasks_4655_; lean_object* v_asyncMode_4656_; uint8_t v_logWrites_4657_; lean_object* v___x_4658_; 
v___x_4645_ = lean_st_ref_take(v___y_4644_);
v_toEnvExtension_4646_ = lean_ctor_get(v___x_4632_, 0);
v_env_4647_ = lean_ctor_get(v___x_4645_, 0);
lean_inc_ref(v_env_4647_);
v_nextMacroScope_4648_ = lean_ctor_get(v___x_4645_, 1);
lean_inc(v_nextMacroScope_4648_);
v_ngen_4649_ = lean_ctor_get(v___x_4645_, 2);
lean_inc_ref(v_ngen_4649_);
v_auxDeclNGen_4650_ = lean_ctor_get(v___x_4645_, 3);
lean_inc_ref(v_auxDeclNGen_4650_);
v_traceState_4651_ = lean_ctor_get(v___x_4645_, 4);
lean_inc_ref(v_traceState_4651_);
v_recordedDeps_4652_ = lean_ctor_get(v___x_4645_, 6);
lean_inc_ref(v_recordedDeps_4652_);
v_messages_4653_ = lean_ctor_get(v___x_4645_, 7);
lean_inc_ref(v_messages_4653_);
v_infoState_4654_ = lean_ctor_get(v___x_4645_, 8);
lean_inc_ref(v_infoState_4654_);
v_snapshotTasks_4655_ = lean_ctor_get(v___x_4645_, 9);
lean_inc_ref(v_snapshotTasks_4655_);
lean_dec(v___x_4645_);
v_asyncMode_4656_ = lean_ctor_get(v_toEnvExtension_4646_, 2);
v_logWrites_4657_ = lean_ctor_get_uint8(v_toEnvExtension_4646_, sizeof(void*)*6);
v___x_4658_ = lean_box(0);
if (v_logWrites_4657_ == 0)
{
lean_object* v___x_4659_; 
lean_inc_ref(v_toEnvExtension_4646_);
v___x_4659_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4646_, v_env_4647_, v___f_4641_, v_asyncMode_4656_, v___x_4634_, v___x_4642_);
v___y_4610_ = v___x_4658_;
v___y_4611_ = v_ngen_4649_;
v___y_4612_ = v___y_4644_;
v___y_4613_ = v_infoState_4654_;
v___y_4614_ = v_recordedDeps_4652_;
v___y_4615_ = v_nextMacroScope_4648_;
v___y_4616_ = v_snapshotTasks_4655_;
v___y_4617_ = v_messages_4653_;
v___y_4618_ = v_auxDeclNGen_4650_;
v___y_4619_ = v_traceState_4651_;
v___y_4620_ = v___x_4659_;
goto v___jp_4609_;
}
else
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
lean_inc_ref_n(v_toEnvExtension_4646_, 2);
v___x_4660_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4646_, v_env_4647_);
lean_dec_ref(v_env_4647_);
v___x_4661_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4646_, v___x_4660_, v___f_4641_, v_asyncMode_4656_, v___x_4634_, v___x_4642_);
v___y_4610_ = v___x_4658_;
v___y_4611_ = v_ngen_4649_;
v___y_4612_ = v___y_4644_;
v___y_4613_ = v_infoState_4654_;
v___y_4614_ = v_recordedDeps_4652_;
v___y_4615_ = v_nextMacroScope_4648_;
v___y_4616_ = v_snapshotTasks_4655_;
v___y_4617_ = v_messages_4653_;
v___y_4618_ = v_auxDeclNGen_4650_;
v___y_4619_ = v_traceState_4651_;
v___y_4620_ = v___x_4661_;
goto v___jp_4609_;
}
}
}
else
{
lean_object* v___x_4695_; lean_object* v___x_4696_; 
lean_dec_ref_known(v_entry_4629_, 1);
lean_dec(v_hint_4605_);
lean_dec(v_mod_4603_);
v___x_4695_ = lean_box(0);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4695_);
return v___x_4696_;
}
v___jp_4609_:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4621_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_addNormTheorem_spec__1___redArg___closed__1);
v___x_4622_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4622_, 0, v___y_4620_);
lean_ctor_set(v___x_4622_, 1, v___y_4615_);
lean_ctor_set(v___x_4622_, 2, v___y_4611_);
lean_ctor_set(v___x_4622_, 3, v___y_4618_);
lean_ctor_set(v___x_4622_, 4, v___y_4619_);
lean_ctor_set(v___x_4622_, 5, v___x_4621_);
lean_ctor_set(v___x_4622_, 6, v___y_4614_);
lean_ctor_set(v___x_4622_, 7, v___y_4617_);
lean_ctor_set(v___x_4622_, 8, v___y_4613_);
lean_ctor_set(v___x_4622_, 9, v___y_4616_);
v___x_4623_ = lean_st_ref_put(v___y_4612_, v___x_4622_);
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v___y_4610_);
return v___x_4624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_4697_, lean_object* v_isMeta_4698_, lean_object* v_hint_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
uint8_t v_isMeta_boxed_4703_; lean_object* v_res_4704_; 
v_isMeta_boxed_4703_ = lean_unbox(v_isMeta_4698_);
v_res_4704_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_4697_, v_isMeta_boxed_4703_, v_hint_4699_, v___y_4700_, v___y_4701_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_4705_, lean_object* v_declName_4706_, lean_object* v_as_4707_, size_t v_sz_4708_, size_t v_i_4709_, lean_object* v_b_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
uint8_t v___x_4714_; 
v___x_4714_ = lean_usize_dec_lt(v_i_4709_, v_sz_4708_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; 
lean_dec(v_declName_4706_);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v_b_4710_);
return v___x_4715_;
}
else
{
lean_object* v___x_4716_; lean_object* v_modules_4717_; lean_object* v___x_4718_; lean_object* v_a_4719_; lean_object* v___x_4720_; lean_object* v_toImport_4721_; lean_object* v_module_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; lean_object* v___x_4725_; 
v___x_4716_ = l_Lean_Environment_header(v___x_4705_);
v_modules_4717_ = lean_ctor_get(v___x_4716_, 3);
lean_inc_ref(v_modules_4717_);
lean_dec_ref(v___x_4716_);
v___x_4718_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4719_ = lean_array_uget_borrowed(v_as_4707_, v_i_4709_);
v___x_4720_ = lean_array_get(v___x_4718_, v_modules_4717_, v_a_4719_);
lean_dec_ref(v_modules_4717_);
v_toImport_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc_ref(v_toImport_4721_);
lean_dec(v___x_4720_);
v_module_4722_ = lean_ctor_get(v_toImport_4721_, 0);
lean_inc(v_module_4722_);
lean_dec_ref(v_toImport_4721_);
v___x_4723_ = lean_box(0);
v___x_4724_ = 0;
lean_inc(v_declName_4706_);
v___x_4725_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4722_, v___x_4724_, v_declName_4706_, v___y_4711_, v___y_4712_);
if (lean_obj_tag(v___x_4725_) == 0)
{
size_t v___x_4726_; size_t v___x_4727_; 
lean_dec_ref_known(v___x_4725_, 1);
v___x_4726_ = ((size_t)1ULL);
v___x_4727_ = lean_usize_add(v_i_4709_, v___x_4726_);
v_i_4709_ = v___x_4727_;
v_b_4710_ = v___x_4723_;
goto _start;
}
else
{
lean_dec(v_declName_4706_);
return v___x_4725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_4729_, lean_object* v_declName_4730_, lean_object* v_as_4731_, lean_object* v_sz_4732_, lean_object* v_i_4733_, lean_object* v_b_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
size_t v_sz_boxed_4738_; size_t v_i_boxed_4739_; lean_object* v_res_4740_; 
v_sz_boxed_4738_ = lean_unbox_usize(v_sz_4732_);
lean_dec(v_sz_4732_);
v_i_boxed_4739_ = lean_unbox_usize(v_i_4733_);
lean_dec(v_i_4733_);
v_res_4740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_4729_, v_declName_4730_, v_as_4731_, v_sz_boxed_4738_, v_i_boxed_4739_, v_b_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec_ref(v_as_4731_);
lean_dec_ref(v___x_4729_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_4741_, uint8_t v_isMeta_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v_env_4751_; lean_object* v___y_4753_; lean_object* v___x_4766_; 
v___x_4746_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_4747_ = lean_st_ref_get(v___y_4744_);
v_env_4751_ = lean_ctor_get(v___x_4747_, 0);
lean_inc_ref(v_env_4751_);
lean_dec(v___x_4747_);
v___x_4766_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4751_, v_declName_4741_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_dec_ref(v_env_4751_);
lean_dec(v_declName_4741_);
goto v___jp_4748_;
}
else
{
lean_object* v_val_4767_; lean_object* v___x_4768_; lean_object* v_modules_4769_; lean_object* v___x_4770_; uint8_t v___x_4771_; 
v_val_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_val_4767_);
lean_dec_ref_known(v___x_4766_, 1);
v___x_4768_ = l_Lean_Environment_header(v_env_4751_);
v_modules_4769_ = lean_ctor_get(v___x_4768_, 3);
lean_inc_ref(v_modules_4769_);
lean_dec_ref(v___x_4768_);
v___x_4770_ = lean_array_get_size(v_modules_4769_);
v___x_4771_ = lean_nat_dec_lt(v_val_4767_, v___x_4770_);
if (v___x_4771_ == 0)
{
lean_dec_ref(v_modules_4769_);
lean_dec(v_val_4767_);
lean_dec_ref(v_env_4751_);
lean_dec(v_declName_4741_);
goto v___jp_4748_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4773_; uint8_t v___y_4775_; 
v___x_4772_ = lean_array_fget(v_modules_4769_, v_val_4767_);
lean_dec(v_val_4767_);
lean_dec_ref(v_modules_4769_);
v___x_4773_ = lean_st_ref_get(v___y_4744_);
if (v_isMeta_4742_ == 0)
{
lean_dec(v___x_4773_);
v___y_4775_ = v_isMeta_4742_;
goto v___jp_4774_;
}
else
{
lean_object* v_env_4786_; uint8_t v___x_4787_; 
v_env_4786_ = lean_ctor_get(v___x_4773_, 0);
lean_inc_ref(v_env_4786_);
lean_dec(v___x_4773_);
lean_inc(v_declName_4741_);
v___x_4787_ = l_Lean_isMarkedMeta(v_env_4786_, v_declName_4741_);
if (v___x_4787_ == 0)
{
v___y_4775_ = v_isMeta_4742_;
goto v___jp_4774_;
}
else
{
uint8_t v___x_4788_; 
v___x_4788_ = 0;
v___y_4775_ = v___x_4788_;
goto v___jp_4774_;
}
}
v___jp_4774_:
{
lean_object* v_toImport_4776_; lean_object* v_module_4777_; lean_object* v___x_4778_; 
v_toImport_4776_ = lean_ctor_get(v___x_4772_, 0);
lean_inc_ref(v_toImport_4776_);
lean_dec(v___x_4772_);
v_module_4777_ = lean_ctor_get(v_toImport_4776_, 0);
lean_inc(v_module_4777_);
lean_dec_ref(v_toImport_4776_);
lean_inc(v_declName_4741_);
v___x_4778_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_4777_, v___y_4775_, v_declName_4741_, v___y_4743_, v___y_4744_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
lean_dec_ref_known(v___x_4778_, 1);
v___x_4779_ = l_Lean_indirectModUseExt;
v___x_4780_ = lean_box(1);
v___x_4781_ = lean_box(0);
lean_inc_ref(v_env_4751_);
v___x_4782_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4746_, v___x_4779_, v_env_4751_, v___x_4780_, v___x_4781_);
v___x_4783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4782_, v_declName_4741_);
lean_dec(v___x_4782_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v___x_4784_; 
v___x_4784_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_4753_ = v___x_4784_;
goto v___jp_4752_;
}
else
{
lean_object* v_val_4785_; 
v_val_4785_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_val_4785_);
lean_dec_ref_known(v___x_4783_, 1);
v___y_4753_ = v_val_4785_;
goto v___jp_4752_;
}
}
else
{
lean_dec_ref(v_env_4751_);
lean_dec(v_declName_4741_);
return v___x_4778_;
}
}
}
}
v___jp_4748_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = lean_box(0);
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
return v___x_4750_;
}
v___jp_4752_:
{
lean_object* v___x_4754_; size_t v_sz_4755_; size_t v___x_4756_; lean_object* v___x_4757_; 
v___x_4754_ = lean_box(0);
v_sz_4755_ = lean_array_size(v___y_4753_);
v___x_4756_ = ((size_t)0ULL);
v___x_4757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_4751_, v_declName_4741_, v___y_4753_, v_sz_4755_, v___x_4756_, v___x_4754_, v___y_4743_, v___y_4744_);
lean_dec_ref(v___y_4753_);
lean_dec_ref(v_env_4751_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4764_ == 0)
{
lean_object* v_unused_4765_; 
v_unused_4765_ = lean_ctor_get(v___x_4757_, 0);
lean_dec(v_unused_4765_);
v___x_4759_ = v___x_4757_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_dec(v___x_4757_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4754_);
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4754_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
else
{
return v___x_4757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_4789_, lean_object* v_isMeta_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
uint8_t v_isMeta_boxed_4794_; lean_object* v_res_4795_; 
v_isMeta_boxed_4794_ = lean_unbox(v_isMeta_4790_);
v_res_4795_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_4789_, v_isMeta_boxed_4794_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4800_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4801_ = lean_st_ref_get(v___x_4800_);
v___x_4802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___redArg(v___x_4801_, v_attrName_4796_);
lean_dec(v___x_4801_);
if (lean_obj_tag(v___x_4802_) == 1)
{
lean_object* v_val_4803_; lean_object* v_ext_4804_; lean_object* v_name_4805_; uint8_t v___x_4806_; lean_object* v___x_4807_; 
v_val_4803_ = lean_ctor_get(v___x_4802_, 0);
v_ext_4804_ = lean_ctor_get(v_val_4803_, 1);
v_name_4805_ = lean_ctor_get(v_ext_4804_, 1);
v___x_4806_ = 1;
lean_inc(v_name_4805_);
v___x_4807_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_4805_, v___x_4806_, v_a_4797_, v_a_4798_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4814_ == 0)
{
lean_object* v_unused_4815_; 
v_unused_4815_ = lean_ctor_get(v___x_4807_, 0);
lean_dec(v_unused_4815_);
v___x_4809_ = v___x_4807_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_dec(v___x_4807_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4802_);
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4802_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec_ref_known(v___x_4802_, 1);
v_a_4816_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4807_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4807_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
else
{
lean_object* v___x_4824_; 
v___x_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4802_);
return v___x_4824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_4825_, v_a_4826_, v_a_4827_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_attrName_4825_);
return v_res_4829_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_4830_; 
v___x_4830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_4831_, lean_object* v_x_4832_){
_start:
{
if (lean_obj_tag(v_x_4832_) == 0)
{
return v_x_4831_;
}
else
{
lean_object* v_key_4833_; lean_object* v_value_4834_; lean_object* v_tail_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4861_; 
v_key_4833_ = lean_ctor_get(v_x_4832_, 0);
v_value_4834_ = lean_ctor_get(v_x_4832_, 1);
v_tail_4835_ = lean_ctor_get(v_x_4832_, 2);
v_isSharedCheck_4861_ = !lean_is_exclusive(v_x_4832_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4837_ = v_x_4832_;
v_isShared_4838_ = v_isSharedCheck_4861_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_tail_4835_);
lean_inc(v_value_4834_);
lean_inc(v_key_4833_);
lean_dec(v_x_4832_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4861_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4839_; uint64_t v___y_4841_; 
v___x_4839_ = lean_array_get_size(v_x_4831_);
if (lean_obj_tag(v_key_4833_) == 0)
{
uint64_t v___x_4859_; 
v___x_4859_ = 1723ULL;
v___y_4841_ = v___x_4859_;
goto v___jp_4840_;
}
else
{
uint64_t v_hash_4860_; 
v_hash_4860_ = lean_ctor_get_uint64(v_key_4833_, sizeof(void*)*2);
v___y_4841_ = v_hash_4860_;
goto v___jp_4840_;
}
v___jp_4840_:
{
uint64_t v___x_4842_; uint64_t v___x_4843_; uint64_t v_fold_4844_; uint64_t v___x_4845_; uint64_t v___x_4846_; uint64_t v___x_4847_; size_t v___x_4848_; size_t v___x_4849_; size_t v___x_4850_; size_t v___x_4851_; size_t v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4855_; 
v___x_4842_ = 32ULL;
v___x_4843_ = lean_uint64_shift_right(v___y_4841_, v___x_4842_);
v_fold_4844_ = lean_uint64_xor(v___y_4841_, v___x_4843_);
v___x_4845_ = 16ULL;
v___x_4846_ = lean_uint64_shift_right(v_fold_4844_, v___x_4845_);
v___x_4847_ = lean_uint64_xor(v_fold_4844_, v___x_4846_);
v___x_4848_ = lean_uint64_to_usize(v___x_4847_);
v___x_4849_ = lean_usize_of_nat(v___x_4839_);
v___x_4850_ = ((size_t)1ULL);
v___x_4851_ = lean_usize_sub(v___x_4849_, v___x_4850_);
v___x_4852_ = lean_usize_land(v___x_4848_, v___x_4851_);
v___x_4853_ = lean_array_uget_borrowed(v_x_4831_, v___x_4852_);
lean_inc(v___x_4853_);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 2, v___x_4853_);
v___x_4855_ = v___x_4837_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_key_4833_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_value_4834_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4856_; 
v___x_4856_ = lean_array_uset(v_x_4831_, v___x_4852_, v___x_4855_);
v_x_4831_ = v___x_4856_;
v_x_4832_ = v_tail_4835_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4862_, lean_object* v_source_4863_, lean_object* v_target_4864_){
_start:
{
lean_object* v___x_4865_; uint8_t v___x_4866_; 
v___x_4865_ = lean_array_get_size(v_source_4863_);
v___x_4866_ = lean_nat_dec_lt(v_i_4862_, v___x_4865_);
if (v___x_4866_ == 0)
{
lean_dec_ref(v_source_4863_);
lean_dec(v_i_4862_);
return v_target_4864_;
}
else
{
lean_object* v_es_4867_; lean_object* v___x_4868_; lean_object* v_source_4869_; lean_object* v_target_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v_es_4867_ = lean_array_fget(v_source_4863_, v_i_4862_);
v___x_4868_ = lean_box(0);
v_source_4869_ = lean_array_fset(v_source_4863_, v_i_4862_, v___x_4868_);
v_target_4870_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_4864_, v_es_4867_);
v___x_4871_ = lean_unsigned_to_nat(1u);
v___x_4872_ = lean_nat_add(v_i_4862_, v___x_4871_);
lean_dec(v_i_4862_);
v_i_4862_ = v___x_4872_;
v_source_4863_ = v_source_4869_;
v_target_4864_ = v_target_4870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_4874_){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v_nbuckets_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4875_ = lean_array_get_size(v_data_4874_);
v___x_4876_ = lean_unsigned_to_nat(2u);
v_nbuckets_4877_ = lean_nat_mul(v___x_4875_, v___x_4876_);
v___x_4878_ = lean_unsigned_to_nat(0u);
v___x_4879_ = lean_box(0);
v___x_4880_ = lean_mk_array(v_nbuckets_4877_, v___x_4879_);
v___x_4881_ = lean_array_propagate_mark(v_data_4874_, v___x_4880_);
v___x_4882_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_4878_, v_data_4874_, v___x_4881_);
return v___x_4882_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_4883_, lean_object* v_x_4884_){
_start:
{
if (lean_obj_tag(v_x_4884_) == 0)
{
uint8_t v___x_4885_; 
v___x_4885_ = 0;
return v___x_4885_;
}
else
{
lean_object* v_key_4886_; lean_object* v_tail_4887_; uint8_t v___x_4888_; 
v_key_4886_ = lean_ctor_get(v_x_4884_, 0);
v_tail_4887_ = lean_ctor_get(v_x_4884_, 2);
v___x_4888_ = lean_name_eq(v_key_4886_, v_a_4883_);
if (v___x_4888_ == 0)
{
v_x_4884_ = v_tail_4887_;
goto _start;
}
else
{
return v___x_4888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_4890_, lean_object* v_x_4891_){
_start:
{
uint8_t v_res_4892_; lean_object* v_r_4893_; 
v_res_4892_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4890_, v_x_4891_);
lean_dec(v_x_4891_);
lean_dec(v_a_4890_);
v_r_4893_ = lean_box(v_res_4892_);
return v_r_4893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_4894_, lean_object* v_b_4895_, lean_object* v_x_4896_){
_start:
{
if (lean_obj_tag(v_x_4896_) == 0)
{
lean_dec(v_b_4895_);
lean_dec(v_a_4894_);
return v_x_4896_;
}
else
{
lean_object* v_key_4897_; lean_object* v_value_4898_; lean_object* v_tail_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4911_; 
v_key_4897_ = lean_ctor_get(v_x_4896_, 0);
v_value_4898_ = lean_ctor_get(v_x_4896_, 1);
v_tail_4899_ = lean_ctor_get(v_x_4896_, 2);
v_isSharedCheck_4911_ = !lean_is_exclusive(v_x_4896_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4901_ = v_x_4896_;
v_isShared_4902_ = v_isSharedCheck_4911_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_tail_4899_);
lean_inc(v_value_4898_);
lean_inc(v_key_4897_);
lean_dec(v_x_4896_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4911_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
uint8_t v___x_4903_; 
v___x_4903_ = lean_name_eq(v_key_4897_, v_a_4894_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4904_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4894_, v_b_4895_, v_tail_4899_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 2, v___x_4904_);
v___x_4906_ = v___x_4901_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_key_4897_);
lean_ctor_set(v_reuseFailAlloc_4907_, 1, v_value_4898_);
lean_ctor_set(v_reuseFailAlloc_4907_, 2, v___x_4904_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
else
{
lean_object* v___x_4909_; 
lean_dec(v_value_4898_);
lean_dec(v_key_4897_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 1, v_b_4895_);
lean_ctor_set(v___x_4901_, 0, v_a_4894_);
v___x_4909_ = v___x_4901_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4894_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_b_4895_);
lean_ctor_set(v_reuseFailAlloc_4910_, 2, v_tail_4899_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_4912_, lean_object* v_a_4913_, lean_object* v_b_4914_){
_start:
{
lean_object* v_size_4915_; lean_object* v_buckets_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4962_; 
v_size_4915_ = lean_ctor_get(v_m_4912_, 0);
v_buckets_4916_ = lean_ctor_get(v_m_4912_, 1);
v_isSharedCheck_4962_ = !lean_is_exclusive(v_m_4912_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4918_ = v_m_4912_;
v_isShared_4919_ = v_isSharedCheck_4962_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_buckets_4916_);
lean_inc(v_size_4915_);
lean_dec(v_m_4912_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4962_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4920_; uint64_t v___y_4922_; 
v___x_4920_ = lean_array_get_size(v_buckets_4916_);
if (lean_obj_tag(v_a_4913_) == 0)
{
uint64_t v___x_4960_; 
v___x_4960_ = 1723ULL;
v___y_4922_ = v___x_4960_;
goto v___jp_4921_;
}
else
{
uint64_t v_hash_4961_; 
v_hash_4961_ = lean_ctor_get_uint64(v_a_4913_, sizeof(void*)*2);
v___y_4922_ = v_hash_4961_;
goto v___jp_4921_;
}
v___jp_4921_:
{
uint64_t v___x_4923_; uint64_t v___x_4924_; uint64_t v_fold_4925_; uint64_t v___x_4926_; uint64_t v___x_4927_; uint64_t v___x_4928_; size_t v___x_4929_; size_t v___x_4930_; size_t v___x_4931_; size_t v___x_4932_; size_t v___x_4933_; lean_object* v_bkt_4934_; uint8_t v___x_4935_; 
v___x_4923_ = 32ULL;
v___x_4924_ = lean_uint64_shift_right(v___y_4922_, v___x_4923_);
v_fold_4925_ = lean_uint64_xor(v___y_4922_, v___x_4924_);
v___x_4926_ = 16ULL;
v___x_4927_ = lean_uint64_shift_right(v_fold_4925_, v___x_4926_);
v___x_4928_ = lean_uint64_xor(v_fold_4925_, v___x_4927_);
v___x_4929_ = lean_uint64_to_usize(v___x_4928_);
v___x_4930_ = lean_usize_of_nat(v___x_4920_);
v___x_4931_ = ((size_t)1ULL);
v___x_4932_ = lean_usize_sub(v___x_4930_, v___x_4931_);
v___x_4933_ = lean_usize_land(v___x_4929_, v___x_4932_);
v_bkt_4934_ = lean_array_uget_borrowed(v_buckets_4916_, v___x_4933_);
v___x_4935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4913_, v_bkt_4934_);
if (v___x_4935_ == 0)
{
lean_object* v___x_4936_; lean_object* v_size_x27_4937_; lean_object* v___x_4938_; lean_object* v_buckets_x27_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; uint8_t v___x_4945_; 
v___x_4936_ = lean_unsigned_to_nat(1u);
v_size_x27_4937_ = lean_nat_add(v_size_4915_, v___x_4936_);
lean_dec(v_size_4915_);
lean_inc(v_bkt_4934_);
v___x_4938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4938_, 0, v_a_4913_);
lean_ctor_set(v___x_4938_, 1, v_b_4914_);
lean_ctor_set(v___x_4938_, 2, v_bkt_4934_);
v_buckets_x27_4939_ = lean_array_uset(v_buckets_4916_, v___x_4933_, v___x_4938_);
v___x_4940_ = lean_unsigned_to_nat(4u);
v___x_4941_ = lean_nat_mul(v_size_x27_4937_, v___x_4940_);
v___x_4942_ = lean_unsigned_to_nat(3u);
v___x_4943_ = lean_nat_div(v___x_4941_, v___x_4942_);
lean_dec(v___x_4941_);
v___x_4944_ = lean_array_get_size(v_buckets_x27_4939_);
v___x_4945_ = lean_nat_dec_le(v___x_4943_, v___x_4944_);
lean_dec(v___x_4943_);
if (v___x_4945_ == 0)
{
lean_object* v_val_4946_; lean_object* v___x_4948_; 
v_val_4946_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_4939_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v_val_4946_);
lean_ctor_set(v___x_4918_, 0, v_size_x27_4937_);
v___x_4948_ = v___x_4918_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_size_x27_4937_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_val_4946_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
else
{
lean_object* v___x_4951_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v_buckets_x27_4939_);
lean_ctor_set(v___x_4918_, 0, v_size_x27_4937_);
v___x_4951_ = v___x_4918_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_size_x27_4937_);
lean_ctor_set(v_reuseFailAlloc_4952_, 1, v_buckets_x27_4939_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
else
{
lean_object* v___x_4953_; lean_object* v_buckets_x27_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4958_; 
lean_inc(v_bkt_4934_);
v___x_4953_ = lean_box(0);
v_buckets_x27_4954_ = lean_array_uset(v_buckets_4916_, v___x_4933_, v___x_4953_);
v___x_4955_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4913_, v_b_4914_, v_bkt_4934_);
v___x_4956_ = lean_array_uset(v_buckets_x27_4954_, v___x_4933_, v___x_4955_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_4956_);
v___x_4958_ = v___x_4918_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_size_4915_);
lean_ctor_set(v_reuseFailAlloc_4959_, 1, v___x_4956_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_4963_, lean_object* v_ref_4964_){
_start:
{
lean_object* v___x_4966_; 
lean_inc(v_ref_4964_);
v___x_4966_ = l_Lean_Meta_Grind_mkExtension(v_ref_4964_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; uint8_t v___x_4968_; uint8_t v___x_4969_; lean_object* v___x_4970_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc_n(v_a_4967_, 2);
lean_dec_ref_known(v___x_4966_, 1);
v___x_4968_ = 0;
v___x_4969_ = 1;
lean_inc(v_ref_4964_);
lean_inc(v_attrName_4963_);
v___x_4970_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4963_, v___x_4968_, v___x_4969_, v_a_4967_, v_ref_4964_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v___x_4971_; 
lean_dec_ref_known(v___x_4970_, 1);
lean_inc(v_ref_4964_);
lean_inc(v_a_4967_);
lean_inc(v_attrName_4963_);
v___x_4971_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4963_, v___x_4968_, v___x_4968_, v_a_4967_, v_ref_4964_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v___x_4972_; 
lean_dec_ref_known(v___x_4971_, 1);
lean_inc(v_ref_4964_);
lean_inc(v_a_4967_);
lean_inc(v_attrName_4963_);
v___x_4972_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4963_, v___x_4969_, v___x_4969_, v_a_4967_, v_ref_4964_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v___x_4973_; 
lean_dec_ref_known(v___x_4972_, 1);
lean_inc(v_a_4967_);
lean_inc(v_attrName_4963_);
v___x_4973_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_4963_, v___x_4969_, v___x_4968_, v_a_4967_, v_ref_4964_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4984_; 
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4984_ == 0)
{
lean_object* v_unused_4985_; 
v_unused_4985_ = lean_ctor_get(v___x_4973_, 0);
lean_dec(v_unused_4985_);
v___x_4975_ = v___x_4973_;
v_isShared_4976_ = v_isSharedCheck_4984_;
goto v_resetjp_4974_;
}
else
{
lean_dec(v___x_4973_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4984_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4982_; 
v___x_4977_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4978_ = lean_st_ref_take(v___x_4977_);
lean_inc(v_a_4967_);
v___x_4979_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4978_, v_attrName_4963_, v_a_4967_);
v___x_4980_ = lean_st_ref_put(v___x_4977_, v___x_4979_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 0, v_a_4967_);
v___x_4982_ = v___x_4975_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4967_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
else
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
lean_dec(v_a_4967_);
lean_dec(v_attrName_4963_);
v_a_4986_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4988_ = v___x_4973_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4973_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4986_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
lean_dec(v_a_4967_);
lean_dec(v_ref_4964_);
lean_dec(v_attrName_4963_);
v_a_4994_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4972_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4972_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4999_; 
if (v_isShared_4997_ == 0)
{
v___x_4999_ = v___x_4996_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4994_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec(v_a_4967_);
lean_dec(v_ref_4964_);
lean_dec(v_attrName_4963_);
v_a_5002_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_4971_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_4971_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
lean_dec(v_a_4967_);
lean_dec(v_ref_4964_);
lean_dec(v_attrName_4963_);
v_a_5010_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_4970_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_4970_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
else
{
lean_dec(v_ref_4964_);
lean_dec(v_attrName_4963_);
return v___x_4966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_5018_, lean_object* v_ref_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Lean_Meta_Grind_registerAttr(v_attrName_5018_, v_ref_5019_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_5022_, lean_object* v_m_5023_, lean_object* v_a_5024_, lean_object* v_b_5025_){
_start:
{
lean_object* v___x_5026_; 
v___x_5026_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_5023_, v_a_5024_, v_b_5025_);
return v___x_5026_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_5027_, lean_object* v_a_5028_, lean_object* v_x_5029_){
_start:
{
uint8_t v___x_5030_; 
v___x_5030_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_5028_, v_x_5029_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5031_, lean_object* v_a_5032_, lean_object* v_x_5033_){
_start:
{
uint8_t v_res_5034_; lean_object* v_r_5035_; 
v_res_5034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_5031_, v_a_5032_, v_x_5033_);
lean_dec(v_x_5033_);
lean_dec(v_a_5032_);
v_r_5035_ = lean_box(v_res_5034_);
return v_r_5035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_5036_, lean_object* v_data_5037_){
_start:
{
lean_object* v___x_5038_; 
v___x_5038_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_5039_, lean_object* v_a_5040_, lean_object* v_b_5041_, lean_object* v_x_5042_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_5040_, v_b_5041_, v_x_5042_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5044_, lean_object* v_i_5045_, lean_object* v_source_5046_, lean_object* v_target_5047_){
_start:
{
lean_object* v___x_5048_; 
v___x_5048_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_5045_, v_source_5046_, v_target_5047_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5049_, lean_object* v_x_5050_, lean_object* v_x_5051_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_5050_, v_x_5051_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8));
v___x_5060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_5061_ = l_Lean_Meta_Grind_registerAttr(v___x_5059_, v___x_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_5076_ = l_Lean_Meta_Grind_registerAttr(v___x_5074_, v___x_5075_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v_env_5084_; lean_object* v___x_5085_; lean_object* v_ext_5086_; lean_object* v_toEnvExtension_5087_; lean_object* v_asyncMode_5088_; uint8_t v___x_5089_; lean_object* v___x_5090_; lean_object* v_casesTypes_5091_; uint8_t v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5082_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_5083_ = lean_st_ref_get(v_a_5080_);
v_env_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc_ref(v_env_5084_);
lean_dec(v___x_5083_);
v___x_5085_ = l_Lean_Meta_Grind_grindExt;
v_ext_5086_ = lean_ctor_get(v___x_5085_, 1);
v_toEnvExtension_5087_ = lean_ctor_get(v_ext_5086_, 0);
v_asyncMode_5088_ = lean_ctor_get(v_toEnvExtension_5087_, 2);
v___x_5089_ = 0;
v___x_5090_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5082_, v___x_5085_, v_env_5084_, v_asyncMode_5088_, v___x_5089_);
v_casesTypes_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc_ref(v_casesTypes_5091_);
lean_dec(v___x_5090_);
v___x_5092_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_5091_, v_declName_5079_);
lean_dec_ref(v_casesTypes_5091_);
v___x_5093_ = lean_box(v___x_5092_);
v___x_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5095_, v_a_5096_);
lean_dec(v_a_5096_);
lean_dec(v_declName_5095_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_5099_, v_a_5101_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_5104_, v_a_5105_, v_a_5106_);
lean_dec(v_a_5106_);
lean_dec_ref(v_a_5105_);
lean_dec(v_declName_5104_);
return v_res_5108_;
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
