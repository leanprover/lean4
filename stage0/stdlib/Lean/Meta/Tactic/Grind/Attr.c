// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Grind.Homo import Lean.Meta.Sym.Simp.Attr import Lean.ExtraModUses
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindHom"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value),LEAN_SCALAR_PTR_LITERAL(14, 226, 234, 13, 148, 139, 225, 180)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object* v_x_15_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(0u);
return v___x_16_;
}
case 1:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(1u);
return v___x_17_;
}
case 2:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(2u);
return v___x_18_;
}
case 3:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(3u);
return v___x_19_;
}
case 4:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(4u);
return v___x_20_;
}
case 5:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(5u);
return v___x_21_;
}
case 6:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(6u);
return v___x_22_;
}
case 7:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(7u);
return v___x_23_;
}
case 8:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(8u);
return v___x_24_;
}
case 9:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(9u);
return v___x_25_;
}
case 10:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(10u);
return v___x_26_;
}
default: 
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(11u);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_AttrKind_ctorIdx(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_30_, lean_object* v_k_31_){
_start:
{
switch(lean_obj_tag(v_t_30_))
{
case 0:
{
lean_object* v_k_32_; lean_object* v___x_33_; 
v_k_32_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_k_32_);
lean_dec_ref_known(v_t_30_, 1);
v___x_33_ = lean_apply_1(v_k_31_, v_k_32_);
return v___x_33_;
}
case 1:
{
uint8_t v_eager_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_eager_34_ = lean_ctor_get_uint8(v_t_30_, 0);
lean_dec_ref_known(v_t_30_, 0);
v___x_35_ = lean_box(v_eager_34_);
v___x_36_ = lean_apply_1(v_k_31_, v___x_35_);
return v___x_36_;
}
case 5:
{
lean_object* v_prio_37_; lean_object* v___x_38_; 
v_prio_37_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_prio_37_);
lean_dec_ref_known(v_t_30_, 1);
v___x_38_ = lean_apply_1(v_k_31_, v_prio_37_);
return v___x_38_;
}
case 8:
{
uint8_t v_post_39_; uint8_t v_inv_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_post_39_ = lean_ctor_get_uint8(v_t_30_, 0);
v_inv_40_ = lean_ctor_get_uint8(v_t_30_, 1);
lean_dec_ref_known(v_t_30_, 0);
v___x_41_ = lean_box(v_post_39_);
v___x_42_ = lean_box(v_inv_40_);
v___x_43_ = lean_apply_2(v_k_31_, v___x_41_, v___x_42_);
return v___x_43_;
}
default: 
{
lean_dec(v_t_30_);
return v_k_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_44_, lean_object* v_ctorIdx_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_k_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_46_, v_k_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_50_, v_ctorIdx_51_, v_t_52_, v_h_53_, v_k_54_);
lean_dec(v_ctorIdx_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_56_, lean_object* v_ematch_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_56_, v_ematch_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_ematch_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_60_, v_ematch_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_64_, lean_object* v_cases_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_64_, v_cases_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_cases_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_68_, v_cases_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_72_, lean_object* v_intro_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_72_, v_intro_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_intro_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_76_, v_intro_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_80_, lean_object* v_infer_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_80_, v_infer_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_infer_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_84_, v_infer_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_88_, lean_object* v_ext_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_88_, v_ext_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_ext_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_92_, v_ext_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_96_, lean_object* v_symbol_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_96_, v_symbol_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_symbol_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_100_, v_symbol_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_104_, lean_object* v_inj_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_104_, v_inj_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_inj_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_108_, v_inj_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_112_, lean_object* v_funCC_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_112_, v_funCC_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_funCC_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_116_, v_funCC_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_120_, lean_object* v_norm_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_120_, v_norm_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_norm_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_124_, v_norm_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_128_, lean_object* v_unfold_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_128_, v_unfold_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_unfold_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_132_, v_unfold_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_136_, lean_object* v_homo_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_136_, v_homo_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_homo_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_140_, v_homo_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_144_, lean_object* v_homoPred_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_144_, v_homoPred_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_homoPred_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_148_, v_homoPred_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set(v___x_157_, 3, v___x_156_);
lean_ctor_set(v___x_157_, 4, v___x_155_);
lean_ctor_set(v___x_157_, 5, v___x_155_);
lean_ctor_set(v___x_157_, 6, v___x_155_);
lean_ctor_set(v___x_157_, 7, v___x_155_);
lean_ctor_set(v___x_157_, 8, v___x_155_);
lean_ctor_set(v___x_157_, 9, v___x_155_);
lean_ctor_set(v___x_157_, 10, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_box(1);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; lean_object* v_toCold_176_; lean_object* v_env_177_; lean_object* v_options_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_175_ = lean_st_ref_get(v___y_173_);
v_toCold_176_ = lean_ctor_get(v___y_172_, 0);
v_env_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_175_);
v_options_178_ = lean_ctor_get(v_toCold_176_, 2);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_178_);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v_env_177_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
lean_ctor_set(v___x_181_, 3, v_options_178_);
v___x_182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_msgData_171_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_ref_193_ = lean_ctor_get(v___y_190_, 2);
v___x_194_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_189_, v___y_190_, v___y_191_);
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_inc(v_ref_193_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_ref_193_);
lean_ctor_set(v___x_199_, 1, v_a_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 1);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_209_, lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_toCold_214_; lean_object* v_currRecDepth_215_; lean_object* v_ref_216_; uint16_t v_optionFlags_217_; uint8_t v_suppressElabErrors_218_; uint8_t v_isRecordingDeps_219_; lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_toCold_214_ = lean_ctor_get(v___y_211_, 0);
v_currRecDepth_215_ = lean_ctor_get(v___y_211_, 1);
v_ref_216_ = lean_ctor_get(v___y_211_, 2);
v_optionFlags_217_ = lean_ctor_get_uint16(v___y_211_, sizeof(void*)*3);
v_suppressElabErrors_218_ = lean_ctor_get_uint8(v___y_211_, sizeof(void*)*3 + 2);
v_isRecordingDeps_219_ = lean_ctor_get_uint8(v___y_211_, sizeof(void*)*3 + 3);
v_ref_220_ = l_Lean_replaceRef(v_ref_209_, v_ref_216_);
lean_inc(v_currRecDepth_215_);
lean_inc_ref(v_toCold_214_);
v___x_221_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_221_, 0, v_toCold_214_);
lean_ctor_set(v___x_221_, 1, v_currRecDepth_215_);
lean_ctor_set(v___x_221_, 2, v_ref_220_);
lean_ctor_set_uint16(v___x_221_, sizeof(void*)*3, v_optionFlags_217_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*3 + 2, v_suppressElabErrors_218_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*3 + 3, v_isRecordingDeps_219_);
v___x_222_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_210_, v___x_221_, v___y_212_);
lean_dec_ref_known(v___x_221_, 3);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_223_, lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_223_, v_msg_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v_ref_223_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__53(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_405_);
v___x_410_ = l_Lean_Syntax_isOfKind(v_stx_405_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_412_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_415_, v_a_406_, v_a_407_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Lean_Syntax_getArg(v_stx_405_, v___x_417_);
v___x_419_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_418_);
v___x_420_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_418_);
v___x_422_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_418_);
v___x_424_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_418_);
v___x_426_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_418_);
v___x_428_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_418_);
v___x_430_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_418_);
v___x_432_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_418_);
v___x_434_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_418_);
v___x_436_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_418_);
v___x_438_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_418_);
v___x_440_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_418_);
v___x_442_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_418_);
v___x_444_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_418_);
v___x_446_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_418_);
v___x_448_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_418_);
v___x_450_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_418_);
v___x_452_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_418_);
v___x_454_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_418_);
v___x_456_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_418_);
v___x_458_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_418_);
v___x_460_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__51));
lean_inc(v___x_418_);
v___x_462_ = l_Lean_Syntax_isOfKind(v___x_418_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v___x_418_);
v___x_463_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_464_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_467_, v_a_406_, v_a_407_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v_stx_405_);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = l_Lean_Syntax_getArg(v___x_418_, v___x_469_);
lean_dec(v___x_418_);
v___x_471_ = l_Lean_Syntax_isNatLit_x3f(v___x_470_);
if (lean_obj_tag(v___x_471_) == 1)
{
lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_480_; 
lean_dec(v___x_470_);
v_val_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_480_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 5);
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_val_472_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v___x_471_);
v___x_481_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__53, &l_Lean_Meta_Grind_getAttrKindCore___closed__53_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__53);
v___x_482_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_470_, v___x_481_, v_a_406_, v_a_407_);
lean_dec(v___x_470_);
return v___x_482_;
}
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_483_ = lean_box(11);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_485_ = lean_box(10);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_487_ = lean_box(9);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = l_Lean_Syntax_getArg(v___x_418_, v___x_489_);
lean_inc(v___x_490_);
v___x_491_ = l_Lean_Syntax_matchesNull(v___x_490_, v___x_417_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
lean_inc(v___x_490_);
v___x_492_ = l_Lean_Syntax_matchesNull(v___x_490_, v___x_489_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v___x_490_);
lean_dec(v___x_418_);
v___x_493_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_494_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_497_, v_a_406_, v_a_407_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = l_Lean_Syntax_getArg(v___x_490_, v___x_417_);
lean_dec(v___x_490_);
v___x_500_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
lean_inc(v___x_499_);
v___x_501_ = l_Lean_Syntax_isOfKind(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_503_ = l_Lean_Syntax_isOfKind(v___x_499_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v___x_418_);
v___x_504_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_505_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_508_, v_a_406_, v_a_407_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_unsigned_to_nat(2u);
v___x_511_ = l_Lean_Syntax_getArg(v___x_418_, v___x_510_);
lean_dec(v___x_418_);
lean_inc(v___x_511_);
v___x_512_ = l_Lean_Syntax_matchesNull(v___x_511_, v___x_417_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
v___x_513_ = l_Lean_Syntax_matchesNull(v___x_511_, v___x_489_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_514_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_515_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_518_, v_a_406_, v_a_407_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_stx_405_);
v___x_520_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_520_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_520_, 1, v___x_410_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v___x_511_);
lean_dec(v_stx_405_);
v___x_522_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_522_, 0, v___x_501_);
lean_ctor_set_uint8(v___x_522_, 1, v___x_501_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
lean_dec(v___x_499_);
v___x_524_ = lean_unsigned_to_nat(2u);
v___x_525_ = l_Lean_Syntax_getArg(v___x_418_, v___x_524_);
lean_dec(v___x_418_);
lean_inc(v___x_525_);
v___x_526_ = l_Lean_Syntax_matchesNull(v___x_525_, v___x_417_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
v___x_527_ = l_Lean_Syntax_matchesNull(v___x_525_, v___x_489_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_528_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_529_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_532_, v_a_406_, v_a_407_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_stx_405_);
v___x_534_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_534_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_534_, 1, v___x_410_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v___x_525_);
lean_dec(v_stx_405_);
v___x_536_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_536_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_536_, 1, v___x_491_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
lean_dec(v___x_490_);
v___x_538_ = lean_unsigned_to_nat(2u);
v___x_539_ = l_Lean_Syntax_getArg(v___x_418_, v___x_538_);
lean_dec(v___x_418_);
lean_inc(v___x_539_);
v___x_540_ = l_Lean_Syntax_matchesNull(v___x_539_, v___x_417_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = l_Lean_Syntax_matchesNull(v___x_539_, v___x_489_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_542_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_543_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_546_, v_a_406_, v_a_407_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_stx_405_);
v___x_548_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_548_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_548_, 1, v___x_410_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v___x_539_);
lean_dec(v_stx_405_);
v___x_550_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_550_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_550_, 1, v___x_452_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_552_ = lean_box(7);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_554_ = lean_box(6);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_556_ = lean_box(4);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_558_ = lean_box(2);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_560_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_560_, 0, v___x_410_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_562_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_562_, 0, v___x_440_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_564_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_564_, 0, v___x_410_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_567_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_569_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_571_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_573_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(3u);
v___x_576_ = l_Lean_Syntax_getArg(v___x_418_, v___x_575_);
lean_dec(v___x_418_);
lean_inc(v___x_576_);
v___x_577_ = l_Lean_Syntax_matchesNull(v___x_576_, v___x_417_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_576_);
v___x_579_ = l_Lean_Syntax_matchesNull(v___x_576_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___x_576_);
v___x_580_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_581_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_584_, v_a_406_, v_a_407_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = l_Lean_Syntax_getArg(v___x_576_, v___x_417_);
lean_dec(v___x_576_);
v___x_587_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_588_ = l_Lean_Syntax_isOfKind(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_589_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_590_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_593_, v_a_406_, v_a_407_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_stx_405_);
v___x_595_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_595_, 0, v___x_410_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v___x_576_);
lean_dec(v_stx_405_);
v___x_598_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_598_, 0, v___x_428_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_unsigned_to_nat(2u);
v___x_602_ = l_Lean_Syntax_getArg(v___x_418_, v___x_601_);
lean_dec(v___x_418_);
lean_inc(v___x_602_);
v___x_603_ = l_Lean_Syntax_matchesNull(v___x_602_, v___x_417_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_602_);
v___x_605_ = l_Lean_Syntax_matchesNull(v___x_602_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v___x_602_);
v___x_606_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_607_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_610_, v_a_406_, v_a_407_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = l_Lean_Syntax_getArg(v___x_602_, v___x_417_);
lean_dec(v___x_602_);
v___x_613_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_614_ = l_Lean_Syntax_isOfKind(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_616_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_619_, v_a_406_, v_a_407_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v_stx_405_);
v___x_621_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_621_, 0, v___x_410_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_602_);
lean_dec(v_stx_405_);
v___x_624_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_624_, 0, v___x_426_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = l_Lean_Syntax_getArg(v___x_418_, v___x_627_);
lean_dec(v___x_418_);
lean_inc(v___x_628_);
v___x_629_ = l_Lean_Syntax_matchesNull(v___x_628_, v___x_417_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
lean_inc(v___x_628_);
v___x_630_ = l_Lean_Syntax_matchesNull(v___x_628_, v___x_627_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v___x_628_);
v___x_631_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_632_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_635_, v_a_406_, v_a_407_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = l_Lean_Syntax_getArg(v___x_628_, v___x_417_);
lean_dec(v___x_628_);
v___x_638_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_639_ = l_Lean_Syntax_isOfKind(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_640_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_641_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_644_, v_a_406_, v_a_407_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_stx_405_);
v___x_646_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_646_, 0, v___x_410_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec(v___x_628_);
lean_dec(v_stx_405_);
v___x_649_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_649_, 0, v___x_424_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v___x_418_);
lean_dec(v_stx_405_);
v___x_652_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = l_Lean_Syntax_getArg(v___x_418_, v___x_654_);
lean_dec(v___x_418_);
lean_inc(v___x_655_);
v___x_656_ = l_Lean_Syntax_matchesNull(v___x_655_, v___x_417_);
if (v___x_656_ == 0)
{
uint8_t v___x_657_; 
lean_inc(v___x_655_);
v___x_657_ = l_Lean_Syntax_matchesNull(v___x_655_, v___x_654_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v___x_655_);
v___x_658_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_659_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_662_, v_a_406_, v_a_407_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_664_ = l_Lean_Syntax_getArg(v___x_655_, v___x_417_);
lean_dec(v___x_655_);
v___x_665_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_666_ = l_Lean_Syntax_isOfKind(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_668_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_671_, v_a_406_, v_a_407_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec(v_stx_405_);
v___x_673_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_673_, 0, v___x_410_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v___x_655_);
lean_dec(v_stx_405_);
v___x_676_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_676_, 0, v___x_420_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = l_Lean_Syntax_getArg(v___x_418_, v___x_679_);
lean_dec(v___x_418_);
lean_inc(v___x_680_);
v___x_681_ = l_Lean_Syntax_matchesNull(v___x_680_, v___x_417_);
if (v___x_681_ == 0)
{
uint8_t v___x_682_; 
lean_inc(v___x_680_);
v___x_682_ = l_Lean_Syntax_matchesNull(v___x_680_, v___x_679_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v___x_680_);
v___x_683_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_684_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_687_, v_a_406_, v_a_407_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = l_Lean_Syntax_getArg(v___x_680_, v___x_417_);
lean_dec(v___x_680_);
v___x_690_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_691_ = l_Lean_Syntax_isOfKind(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_692_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_693_ = l_Lean_MessageData_ofSyntax(v_stx_405_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_696_, v_a_406_, v_a_407_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v_stx_405_);
v___x_698_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_698_, 0, v___x_410_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v___x_680_);
lean_dec(v_stx_405_);
v___x_701_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_708_, lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_709_, v___y_710_, v___y_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_714_, v_msg_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_720_, lean_object* v_ref_721_, lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_721_, v_msg_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_727_, lean_object* v_ref_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_727_, v_ref_728_, v_msg_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_ref_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = l_Lean_Syntax_getArg(v_stx_734_, v___x_738_);
v___x_740_ = l_Lean_Syntax_isNone(v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = l_Lean_Syntax_getArg(v___x_739_, v___x_741_);
lean_dec(v___x_739_);
v___x_743_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_742_, v_a_735_, v_a_736_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec(v___x_739_);
v___x_744_ = lean_box(3);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_stx_746_);
return v_res_750_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_758_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_757_, v_a_754_, v_a_755_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_764_, v_a_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_772_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_777_, lean_object* v_b_778_, uint8_t v_kind_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_toCold_783_; lean_object* v_currNamespace_784_; lean_object* v___x_785_; lean_object* v_env_786_; lean_object* v_nextMacroScope_787_; lean_object* v_ngen_788_; lean_object* v_auxDeclNGen_789_; lean_object* v_traceState_790_; lean_object* v_recordedDeps_791_; lean_object* v_messages_792_; lean_object* v_infoState_793_; lean_object* v_snapshotTasks_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_806_; 
v_toCold_783_ = lean_ctor_get(v___y_780_, 0);
v_currNamespace_784_ = lean_ctor_get(v_toCold_783_, 4);
v___x_785_ = lean_st_ref_take(v___y_781_);
v_env_786_ = lean_ctor_get(v___x_785_, 0);
v_nextMacroScope_787_ = lean_ctor_get(v___x_785_, 1);
v_ngen_788_ = lean_ctor_get(v___x_785_, 2);
v_auxDeclNGen_789_ = lean_ctor_get(v___x_785_, 3);
v_traceState_790_ = lean_ctor_get(v___x_785_, 4);
v_recordedDeps_791_ = lean_ctor_get(v___x_785_, 6);
v_messages_792_ = lean_ctor_get(v___x_785_, 7);
v_infoState_793_ = lean_ctor_get(v___x_785_, 8);
v_snapshotTasks_794_ = lean_ctor_get(v___x_785_, 9);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v___x_785_, 5);
lean_dec(v_unused_807_);
v___x_796_ = v___x_785_;
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_snapshotTasks_794_);
lean_inc(v_infoState_793_);
lean_inc(v_messages_792_);
lean_inc(v_recordedDeps_791_);
lean_inc(v_traceState_790_);
lean_inc(v_auxDeclNGen_789_);
lean_inc(v_ngen_788_);
lean_inc(v_nextMacroScope_787_);
lean_inc(v_env_786_);
lean_dec(v___x_785_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_806_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_798_ = lean_box(0);
lean_inc(v_currNamespace_784_);
v___x_799_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_786_, v_ext_777_, v_b_778_, v_kind_779_, v_currNamespace_784_);
v___x_800_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 5, v___x_800_);
lean_ctor_set(v___x_796_, 0, v___x_799_);
v___x_802_ = v___x_796_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_nextMacroScope_787_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_ngen_788_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_auxDeclNGen_789_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_traceState_790_);
lean_ctor_set(v_reuseFailAlloc_805_, 5, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 6, v_recordedDeps_791_);
lean_ctor_set(v_reuseFailAlloc_805_, 7, v_messages_792_);
lean_ctor_set(v_reuseFailAlloc_805_, 8, v_infoState_793_);
lean_ctor_set(v_reuseFailAlloc_805_, 9, v_snapshotTasks_794_);
v___x_802_ = v_reuseFailAlloc_805_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_st_ref_put(v___y_781_, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_798_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_808_, lean_object* v_b_809_, lean_object* v_kind_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v_kind_boxed_814_; lean_object* v_res_815_; 
v_kind_boxed_814_ = lean_unbox(v_kind_810_);
v_res_815_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_808_, v_b_809_, v_kind_boxed_814_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_00_u03c3_818_, lean_object* v_ext_819_, lean_object* v_b_820_, uint8_t v_kind_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_819_, v_b_820_, v_kind_821_, v___y_822_, v___y_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_00_u03c3_828_, lean_object* v_ext_829_, lean_object* v_b_830_, lean_object* v_kind_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v_kind_boxed_835_; lean_object* v_res_836_; 
v_kind_boxed_835_ = lean_unbox(v_kind_831_);
v_res_836_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_826_, v_00_u03b2_827_, v_00_u03c3_828_, v_ext_829_, v_b_830_, v_kind_boxed_835_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_837_, lean_object* v_declName_838_, uint8_t v_eager_839_, uint8_t v_attrKind_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; 
lean_inc(v_declName_838_);
v___x_844_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_838_, v_eager_839_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec_ref_known(v___x_844_, 1);
v___x_845_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_845_, 0, v_declName_838_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*1, v_eager_839_);
v___x_846_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_837_, v___x_845_, v_attrKind_840_, v_a_841_, v_a_842_);
return v___x_846_;
}
else
{
lean_dec(v_declName_838_);
lean_dec_ref(v_ext_837_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_847_, lean_object* v_declName_848_, lean_object* v_eager_849_, lean_object* v_attrKind_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
uint8_t v_eager_boxed_854_; uint8_t v_attrKind_boxed_855_; lean_object* v_res_856_; 
v_eager_boxed_854_ = lean_unbox(v_eager_849_);
v_attrKind_boxed_855_ = lean_unbox(v_attrKind_850_);
v_res_856_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_847_, v_declName_848_, v_eager_boxed_854_, v_attrKind_boxed_855_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_857_, lean_object* v_declName_858_, uint8_t v_attrKind_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
lean_inc(v_declName_858_);
v___x_863_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_858_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_872_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_declName_858_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_declName_858_);
v___x_868_ = v_reuseFailAlloc_870_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_857_, v___x_868_, v_attrKind_859_, v_a_860_, v_a_861_);
return v___x_869_;
}
}
}
else
{
lean_dec(v_declName_858_);
lean_dec_ref(v_ext_857_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_873_, lean_object* v_declName_874_, lean_object* v_attrKind_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
uint8_t v_attrKind_boxed_879_; lean_object* v_res_880_; 
v_attrKind_boxed_879_ = lean_unbox(v_attrKind_875_);
v_res_880_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_873_, v_declName_874_, v_attrKind_boxed_879_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_881_, lean_object* v_declName_882_, uint8_t v_attrKind_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_declName_882_);
v___x_888_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_881_, v___x_887_, v_attrKind_883_, v_a_884_, v_a_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_889_, lean_object* v_declName_890_, lean_object* v_attrKind_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
uint8_t v_attrKind_boxed_895_; lean_object* v_res_896_; 
v_attrKind_boxed_895_ = lean_unbox(v_attrKind_891_);
v_res_896_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_889_, v_declName_890_, v_attrKind_boxed_895_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_897_, lean_object* v_s_898_){
_start:
{
lean_object* v_casesTypes_899_; lean_object* v_funCC_900_; lean_object* v_ematch_901_; lean_object* v_inj_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_casesTypes_899_ = lean_ctor_get(v_s_898_, 0);
v_funCC_900_ = lean_ctor_get(v_s_898_, 2);
v_ematch_901_ = lean_ctor_get(v_s_898_, 3);
v_inj_902_ = lean_ctor_get(v_s_898_, 4);
v_isSharedCheck_909_ = !lean_is_exclusive(v_s_898_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_s_898_, 1);
lean_dec(v_unused_910_);
v___x_904_ = v_s_898_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_inj_902_);
lean_inc(v_ematch_901_);
lean_inc(v_funCC_900_);
lean_inc(v_casesTypes_899_);
lean_dec(v_s_898_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_a_897_);
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_casesTypes_899_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_a_897_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_funCC_900_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_ematch_901_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v_inj_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_911_, lean_object* v_declName_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_ext_918_; lean_object* v_toEnvExtension_919_; lean_object* v_env_920_; lean_object* v_asyncMode_921_; lean_object* v___x_922_; lean_object* v_extThms_923_; lean_object* v___x_924_; 
v___x_916_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_917_ = lean_st_ref_get(v_a_914_);
v_ext_918_ = lean_ctor_get(v_ext_911_, 1);
v_toEnvExtension_919_ = lean_ctor_get(v_ext_918_, 0);
v_env_920_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_env_920_);
lean_dec(v___x_917_);
v_asyncMode_921_ = lean_ctor_get(v_toEnvExtension_919_, 2);
v___x_922_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_916_, v_ext_911_, v_env_920_, v_asyncMode_921_);
v_extThms_923_ = lean_ctor_get(v___x_922_, 1);
lean_inc_ref(v_extThms_923_);
lean_dec(v___x_922_);
v___x_924_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_923_, v_declName_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_955_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_955_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_955_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_955_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v_env_931_; lean_object* v_nextMacroScope_932_; lean_object* v_ngen_933_; lean_object* v_auxDeclNGen_934_; lean_object* v_traceState_935_; lean_object* v_recordedDeps_936_; lean_object* v_messages_937_; lean_object* v_infoState_938_; lean_object* v_snapshotTasks_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_953_; 
v___f_929_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_929_, 0, v_a_925_);
v___x_930_ = lean_st_ref_take(v_a_914_);
v_env_931_ = lean_ctor_get(v___x_930_, 0);
v_nextMacroScope_932_ = lean_ctor_get(v___x_930_, 1);
v_ngen_933_ = lean_ctor_get(v___x_930_, 2);
v_auxDeclNGen_934_ = lean_ctor_get(v___x_930_, 3);
v_traceState_935_ = lean_ctor_get(v___x_930_, 4);
v_recordedDeps_936_ = lean_ctor_get(v___x_930_, 6);
v_messages_937_ = lean_ctor_get(v___x_930_, 7);
v_infoState_938_ = lean_ctor_get(v___x_930_, 8);
v_snapshotTasks_939_ = lean_ctor_get(v___x_930_, 9);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v___x_930_, 5);
lean_dec(v_unused_954_);
v___x_941_ = v___x_930_;
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snapshotTasks_939_);
lean_inc(v_infoState_938_);
lean_inc(v_messages_937_);
lean_inc(v_recordedDeps_936_);
lean_inc(v_traceState_935_);
lean_inc(v_auxDeclNGen_934_);
lean_inc(v_ngen_933_);
lean_inc(v_nextMacroScope_932_);
lean_inc(v_env_931_);
lean_dec(v___x_930_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_943_ = lean_box(0);
v___x_944_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_911_, v_env_931_, v___f_929_);
v___x_945_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 5, v___x_945_);
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_947_ = v___x_941_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_nextMacroScope_932_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_ngen_933_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_auxDeclNGen_934_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_traceState_935_);
lean_ctor_set(v_reuseFailAlloc_952_, 5, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 6, v_recordedDeps_936_);
lean_ctor_set(v_reuseFailAlloc_952_, 7, v_messages_937_);
lean_ctor_set(v_reuseFailAlloc_952_, 8, v_infoState_938_);
lean_ctor_set(v_reuseFailAlloc_952_, 9, v_snapshotTasks_939_);
v___x_947_ = v_reuseFailAlloc_952_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_st_ref_put(v_a_914_, v___x_947_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_943_);
v___x_950_ = v___x_927_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_943_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_ext_911_);
v_a_956_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_924_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_924_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_964_, lean_object* v_declName_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_964_, v_declName_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_970_, lean_object* v_s_971_){
_start:
{
lean_object* v_extThms_972_; lean_object* v_funCC_973_; lean_object* v_ematch_974_; lean_object* v_inj_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_extThms_972_ = lean_ctor_get(v_s_971_, 1);
v_funCC_973_ = lean_ctor_get(v_s_971_, 2);
v_ematch_974_ = lean_ctor_get(v_s_971_, 3);
v_inj_975_ = lean_ctor_get(v_s_971_, 4);
v_isSharedCheck_982_ = !lean_is_exclusive(v_s_971_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_s_971_, 0);
lean_dec(v_unused_983_);
v___x_977_ = v_s_971_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_inj_975_);
lean_inc(v_ematch_974_);
lean_inc(v_funCC_973_);
lean_inc(v_extThms_972_);
lean_dec(v_s_971_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_a_970_);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_extThms_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_funCC_973_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_ematch_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_inj_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_984_, lean_object* v_declName_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_985_);
v___x_990_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; lean_object* v_ext_992_; lean_object* v_toEnvExtension_993_; lean_object* v_env_994_; lean_object* v_asyncMode_995_; lean_object* v___x_996_; lean_object* v_casesTypes_997_; lean_object* v___x_998_; 
lean_dec_ref_known(v___x_990_, 1);
v___x_991_ = lean_st_ref_get(v_a_987_);
v_ext_992_ = lean_ctor_get(v_ext_984_, 1);
v_toEnvExtension_993_ = lean_ctor_get(v_ext_992_, 0);
v_env_994_ = lean_ctor_get(v___x_991_, 0);
lean_inc_ref(v_env_994_);
lean_dec(v___x_991_);
v_asyncMode_995_ = lean_ctor_get(v_toEnvExtension_993_, 2);
v___x_996_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_989_, v_ext_984_, v_env_994_, v_asyncMode_995_);
v_casesTypes_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc_ref(v_casesTypes_997_);
lean_dec(v___x_996_);
v___x_998_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_997_, v_declName_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1029_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1029_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1029_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v_env_1005_; lean_object* v_nextMacroScope_1006_; lean_object* v_ngen_1007_; lean_object* v_auxDeclNGen_1008_; lean_object* v_traceState_1009_; lean_object* v_recordedDeps_1010_; lean_object* v_messages_1011_; lean_object* v_infoState_1012_; lean_object* v_snapshotTasks_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1027_; 
v___f_1003_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1003_, 0, v_a_999_);
v___x_1004_ = lean_st_ref_take(v_a_987_);
v_env_1005_ = lean_ctor_get(v___x_1004_, 0);
v_nextMacroScope_1006_ = lean_ctor_get(v___x_1004_, 1);
v_ngen_1007_ = lean_ctor_get(v___x_1004_, 2);
v_auxDeclNGen_1008_ = lean_ctor_get(v___x_1004_, 3);
v_traceState_1009_ = lean_ctor_get(v___x_1004_, 4);
v_recordedDeps_1010_ = lean_ctor_get(v___x_1004_, 6);
v_messages_1011_ = lean_ctor_get(v___x_1004_, 7);
v_infoState_1012_ = lean_ctor_get(v___x_1004_, 8);
v_snapshotTasks_1013_ = lean_ctor_get(v___x_1004_, 9);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v___x_1004_, 5);
lean_dec(v_unused_1028_);
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1027_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snapshotTasks_1013_);
lean_inc(v_infoState_1012_);
lean_inc(v_messages_1011_);
lean_inc(v_recordedDeps_1010_);
lean_inc(v_traceState_1009_);
lean_inc(v_auxDeclNGen_1008_);
lean_inc(v_ngen_1007_);
lean_inc(v_nextMacroScope_1006_);
lean_inc(v_env_1005_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1027_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_984_, v_env_1005_, v___f_1003_);
v___x_1019_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 5, v___x_1019_);
lean_ctor_set(v___x_1015_, 0, v___x_1018_);
v___x_1021_ = v___x_1015_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_nextMacroScope_1006_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_ngen_1007_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_auxDeclNGen_1008_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v_traceState_1009_);
lean_ctor_set(v_reuseFailAlloc_1026_, 5, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1026_, 6, v_recordedDeps_1010_);
lean_ctor_set(v_reuseFailAlloc_1026_, 7, v_messages_1011_);
lean_ctor_set(v_reuseFailAlloc_1026_, 8, v_infoState_1012_);
lean_ctor_set(v_reuseFailAlloc_1026_, 9, v_snapshotTasks_1013_);
v___x_1021_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = lean_st_ref_put(v_a_987_, v___x_1021_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1017_);
v___x_1024_ = v___x_1001_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1017_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref(v_ext_984_);
v_a_1030_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_998_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_998_);
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
else
{
lean_dec(v_declName_985_);
lean_dec_ref(v_ext_984_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1038_, lean_object* v_declName_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1038_, v_declName_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1044_, lean_object* v_s_1045_){
_start:
{
lean_object* v_casesTypes_1046_; lean_object* v_extThms_1047_; lean_object* v_ematch_1048_; lean_object* v_inj_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
v_casesTypes_1046_ = lean_ctor_get(v_s_1045_, 0);
v_extThms_1047_ = lean_ctor_get(v_s_1045_, 1);
v_ematch_1048_ = lean_ctor_get(v_s_1045_, 3);
v_inj_1049_ = lean_ctor_get(v_s_1045_, 4);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_s_1045_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v_s_1045_, 2);
lean_dec(v_unused_1057_);
v___x_1051_ = v_s_1045_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_inj_1049_);
lean_inc(v_ematch_1048_);
lean_inc(v_extThms_1047_);
lean_inc(v_casesTypes_1046_);
lean_dec(v_s_1045_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 2, v___x_1044_);
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_casesTypes_1046_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_extThms_1047_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1055_, 3, v_ematch_1048_);
lean_ctor_set(v_reuseFailAlloc_1055_, 4, v_inj_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1058_, lean_object* v_t_1059_){
_start:
{
if (lean_obj_tag(v_t_1059_) == 0)
{
lean_object* v_k_1060_; lean_object* v_v_1061_; lean_object* v_l_1062_; lean_object* v_r_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1717_; 
v_k_1060_ = lean_ctor_get(v_t_1059_, 1);
v_v_1061_ = lean_ctor_get(v_t_1059_, 2);
v_l_1062_ = lean_ctor_get(v_t_1059_, 3);
v_r_1063_ = lean_ctor_get(v_t_1059_, 4);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_t_1059_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v_t_1059_, 0);
lean_dec(v_unused_1718_);
v___x_1065_ = v_t_1059_;
v_isShared_1066_ = v_isSharedCheck_1717_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_r_1063_);
lean_inc(v_l_1062_);
lean_inc(v_v_1061_);
lean_inc(v_k_1060_);
lean_dec(v_t_1059_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1717_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint8_t v___x_1067_; 
v___x_1067_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1058_, v_k_1060_);
switch(v___x_1067_)
{
case 0:
{
lean_object* v_impl_1068_; lean_object* v___x_1069_; 
v_impl_1068_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1058_, v_l_1062_);
v___x_1069_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1068_) == 0)
{
if (lean_obj_tag(v_r_1063_) == 0)
{
lean_object* v_size_1070_; lean_object* v_size_1071_; lean_object* v_k_1072_; lean_object* v_v_1073_; lean_object* v_l_1074_; lean_object* v_r_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_size_1070_ = lean_ctor_get(v_impl_1068_, 0);
lean_inc(v_size_1070_);
v_size_1071_ = lean_ctor_get(v_r_1063_, 0);
v_k_1072_ = lean_ctor_get(v_r_1063_, 1);
v_v_1073_ = lean_ctor_get(v_r_1063_, 2);
v_l_1074_ = lean_ctor_get(v_r_1063_, 3);
lean_inc(v_l_1074_);
v_r_1075_ = lean_ctor_get(v_r_1063_, 4);
v___x_1076_ = lean_unsigned_to_nat(3u);
v___x_1077_ = lean_nat_mul(v___x_1076_, v_size_1070_);
v___x_1078_ = lean_nat_dec_lt(v___x_1077_, v_size_1071_);
lean_dec(v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
lean_dec(v_l_1074_);
v___x_1079_ = lean_nat_add(v___x_1069_, v_size_1070_);
lean_dec(v_size_1070_);
v___x_1080_ = lean_nat_add(v___x_1079_, v_size_1071_);
lean_dec(v___x_1079_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 3, v_impl_1068_);
lean_ctor_set(v___x_1065_, 0, v___x_1080_);
v___x_1082_ = v___x_1065_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_impl_1068_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_r_1063_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1147_; 
lean_inc(v_r_1075_);
lean_inc(v_v_1073_);
lean_inc(v_k_1072_);
lean_inc(v_size_1071_);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1148_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_r_1063_, 2);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1063_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_r_1063_, 0);
lean_dec(v_unused_1152_);
v___x_1085_ = v_r_1063_;
v_isShared_1086_ = v_isSharedCheck_1147_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v_r_1063_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1147_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_size_1087_; lean_object* v_k_1088_; lean_object* v_v_1089_; lean_object* v_l_1090_; lean_object* v_r_1091_; lean_object* v_size_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_size_1087_ = lean_ctor_get(v_l_1074_, 0);
v_k_1088_ = lean_ctor_get(v_l_1074_, 1);
v_v_1089_ = lean_ctor_get(v_l_1074_, 2);
v_l_1090_ = lean_ctor_get(v_l_1074_, 3);
v_r_1091_ = lean_ctor_get(v_l_1074_, 4);
v_size_1092_ = lean_ctor_get(v_r_1075_, 0);
v___x_1093_ = lean_unsigned_to_nat(2u);
v___x_1094_ = lean_nat_mul(v___x_1093_, v_size_1092_);
v___x_1095_ = lean_nat_dec_lt(v_size_1087_, v___x_1094_);
lean_dec(v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1123_; 
lean_inc(v_r_1091_);
lean_inc(v_l_1090_);
lean_inc(v_v_1089_);
lean_inc(v_k_1088_);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_l_1074_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; lean_object* v_unused_1125_; lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; 
v_unused_1124_ = lean_ctor_get(v_l_1074_, 4);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_l_1074_, 3);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_l_1074_, 2);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_l_1074_, 1);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_l_1074_, 0);
lean_dec(v_unused_1128_);
v___x_1097_ = v_l_1074_;
v_isShared_1098_ = v_isSharedCheck_1123_;
goto v_resetjp_1096_;
}
else
{
lean_dec(v_l_1074_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1123_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1113_; 
v___x_1099_ = lean_nat_add(v___x_1069_, v_size_1070_);
lean_dec(v_size_1070_);
v___x_1100_ = lean_nat_add(v___x_1099_, v_size_1071_);
lean_dec(v_size_1071_);
if (lean_obj_tag(v_l_1090_) == 0)
{
lean_object* v_size_1121_; 
v_size_1121_ = lean_ctor_get(v_l_1090_, 0);
lean_inc(v_size_1121_);
v___y_1113_ = v_size_1121_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
v___y_1113_ = v___x_1122_;
goto v___jp_1112_;
}
v___jp_1101_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_nat_add(v___y_1102_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec(v___y_1102_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 4, v_r_1075_);
lean_ctor_set(v___x_1097_, 3, v_r_1091_);
lean_ctor_set(v___x_1097_, 2, v_v_1073_);
lean_ctor_set(v___x_1097_, 1, v_k_1072_);
lean_ctor_set(v___x_1097_, 0, v___x_1105_);
v___x_1107_ = v___x_1097_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_k_1072_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_v_1073_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_r_1091_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v_r_1075_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 4, v___x_1107_);
lean_ctor_set(v___x_1085_, 3, v___y_1103_);
lean_ctor_set(v___x_1085_, 2, v_v_1089_);
lean_ctor_set(v___x_1085_, 1, v_k_1088_);
lean_ctor_set(v___x_1085_, 0, v___x_1100_);
v___x_1109_ = v___x_1085_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_k_1088_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_v_1089_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v___y_1103_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
v___jp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_nat_add(v___x_1099_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec(v___x_1099_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_l_1090_);
lean_ctor_set(v___x_1065_, 3, v_impl_1068_);
lean_ctor_set(v___x_1065_, 0, v___x_1114_);
v___x_1116_ = v___x_1065_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_impl_1068_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_l_1090_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_nat_add(v___x_1069_, v_size_1092_);
if (lean_obj_tag(v_r_1091_) == 0)
{
lean_object* v_size_1118_; 
v_size_1118_ = lean_ctor_get(v_r_1091_, 0);
lean_inc(v_size_1118_);
v___y_1102_ = v___x_1117_;
v___y_1103_ = v___x_1116_;
v___y_1104_ = v_size_1118_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___y_1102_ = v___x_1117_;
v___y_1103_ = v___x_1116_;
v___y_1104_ = v___x_1119_;
goto v___jp_1101_;
}
}
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
lean_del_object(v___x_1065_);
v___x_1129_ = lean_nat_add(v___x_1069_, v_size_1070_);
lean_dec(v_size_1070_);
v___x_1130_ = lean_nat_add(v___x_1129_, v_size_1071_);
lean_dec(v_size_1071_);
v___x_1131_ = lean_nat_add(v___x_1129_, v_size_1087_);
lean_dec(v___x_1129_);
lean_inc_ref(v_impl_1068_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 4, v_l_1074_);
lean_ctor_set(v___x_1085_, 3, v_impl_1068_);
lean_ctor_set(v___x_1085_, 2, v_v_1061_);
lean_ctor_set(v___x_1085_, 1, v_k_1060_);
lean_ctor_set(v___x_1085_, 0, v___x_1131_);
v___x_1133_ = v___x_1085_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_impl_1068_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_l_1074_);
v___x_1133_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_isSharedCheck_1140_ = !lean_is_exclusive(v_impl_1068_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1141_ = lean_ctor_get(v_impl_1068_, 4);
lean_dec(v_unused_1141_);
v_unused_1142_ = lean_ctor_get(v_impl_1068_, 3);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_impl_1068_, 2);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_impl_1068_, 1);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_impl_1068_, 0);
lean_dec(v_unused_1145_);
v___x_1135_ = v_impl_1068_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v_impl_1068_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 4, v_r_1075_);
lean_ctor_set(v___x_1135_, 3, v___x_1133_);
lean_ctor_set(v___x_1135_, 2, v_v_1073_);
lean_ctor_set(v___x_1135_, 1, v_k_1072_);
lean_ctor_set(v___x_1135_, 0, v___x_1130_);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1072_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1073_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_r_1075_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v_size_1153_ = lean_ctor_get(v_impl_1068_, 0);
lean_inc(v_size_1153_);
v___x_1154_ = lean_nat_add(v___x_1069_, v_size_1153_);
lean_dec(v_size_1153_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 3, v_impl_1068_);
lean_ctor_set(v___x_1065_, 0, v___x_1154_);
v___x_1156_ = v___x_1065_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_impl_1068_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_r_1063_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
if (lean_obj_tag(v_r_1063_) == 0)
{
lean_object* v_l_1158_; 
v_l_1158_ = lean_ctor_get(v_r_1063_, 3);
lean_inc(v_l_1158_);
if (lean_obj_tag(v_l_1158_) == 0)
{
lean_object* v_r_1159_; 
v_r_1159_ = lean_ctor_get(v_r_1063_, 4);
lean_inc(v_r_1159_);
if (lean_obj_tag(v_r_1159_) == 0)
{
lean_object* v_size_1160_; lean_object* v_k_1161_; lean_object* v_v_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1175_; 
v_size_1160_ = lean_ctor_get(v_r_1063_, 0);
v_k_1161_ = lean_ctor_get(v_r_1063_, 1);
v_v_1162_ = lean_ctor_get(v_r_1063_, 2);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; lean_object* v_unused_1177_; 
v_unused_1176_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1177_);
v___x_1164_ = v_r_1063_;
v_isShared_1165_ = v_isSharedCheck_1175_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_v_1162_);
lean_inc(v_k_1161_);
lean_inc(v_size_1160_);
lean_dec(v_r_1063_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1175_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_size_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v_size_1166_ = lean_ctor_get(v_l_1158_, 0);
v___x_1167_ = lean_nat_add(v___x_1069_, v_size_1160_);
lean_dec(v_size_1160_);
v___x_1168_ = lean_nat_add(v___x_1069_, v_size_1166_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 4, v_l_1158_);
lean_ctor_set(v___x_1164_, 3, v_impl_1068_);
lean_ctor_set(v___x_1164_, 2, v_v_1061_);
lean_ctor_set(v___x_1164_, 1, v_k_1060_);
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1170_ = v___x_1164_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_impl_1068_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_l_1158_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_r_1159_);
lean_ctor_set(v___x_1065_, 3, v___x_1170_);
lean_ctor_set(v___x_1065_, 2, v_v_1162_);
lean_ctor_set(v___x_1065_, 1, v_k_1161_);
lean_ctor_set(v___x_1065_, 0, v___x_1167_);
v___x_1172_ = v___x_1065_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_k_1161_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_v_1162_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_r_1159_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_k_1178_; lean_object* v_v_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1202_; 
v_k_1178_ = lean_ctor_get(v_r_1063_, 1);
v_v_1179_ = lean_ctor_get(v_r_1063_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; 
v_unused_1203_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_r_1063_, 0);
lean_dec(v_unused_1205_);
v___x_1181_ = v_r_1063_;
v_isShared_1182_ = v_isSharedCheck_1202_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_v_1179_);
lean_inc(v_k_1178_);
lean_dec(v_r_1063_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1202_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_k_1183_; lean_object* v_v_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1198_; 
v_k_1183_ = lean_ctor_get(v_l_1158_, 1);
v_v_1184_ = lean_ctor_get(v_l_1158_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_l_1158_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; lean_object* v_unused_1201_; 
v_unused_1199_ = lean_ctor_get(v_l_1158_, 4);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_l_1158_, 3);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_l_1158_, 0);
lean_dec(v_unused_1201_);
v___x_1186_ = v_l_1158_;
v_isShared_1187_ = v_isSharedCheck_1198_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_v_1184_);
lean_inc(v_k_1183_);
lean_dec(v_l_1158_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1198_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_unsigned_to_nat(3u);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 4, v_r_1159_);
lean_ctor_set(v___x_1186_, 3, v_r_1159_);
lean_ctor_set(v___x_1186_, 2, v_v_1061_);
lean_ctor_set(v___x_1186_, 1, v_k_1060_);
lean_ctor_set(v___x_1186_, 0, v___x_1069_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_r_1159_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_r_1159_);
v___x_1190_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 3, v_r_1159_);
lean_ctor_set(v___x_1181_, 0, v___x_1069_);
v___x_1192_ = v___x_1181_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_k_1178_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_v_1179_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_r_1159_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_r_1159_);
v___x_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1194_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1192_);
lean_ctor_set(v___x_1065_, 3, v___x_1190_);
lean_ctor_set(v___x_1065_, 2, v_v_1184_);
lean_ctor_set(v___x_1065_, 1, v_k_1183_);
lean_ctor_set(v___x_1065_, 0, v___x_1188_);
v___x_1194_ = v___x_1065_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_k_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_v_1184_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v___x_1192_);
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
}
}
}
else
{
lean_object* v_r_1206_; 
v_r_1206_ = lean_ctor_get(v_r_1063_, 4);
lean_inc(v_r_1206_);
if (lean_obj_tag(v_r_1206_) == 0)
{
lean_object* v_k_1207_; lean_object* v_v_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1219_; 
v_k_1207_ = lean_ctor_get(v_r_1063_, 1);
v_v_1208_ = lean_ctor_get(v_r_1063_, 2);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; 
v_unused_1220_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_r_1063_, 0);
lean_dec(v_unused_1222_);
v___x_1210_ = v_r_1063_;
v_isShared_1211_ = v_isSharedCheck_1219_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_v_1208_);
lean_inc(v_k_1207_);
lean_dec(v_r_1063_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1219_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_unsigned_to_nat(3u);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 4, v_l_1158_);
lean_ctor_set(v___x_1210_, 2, v_v_1061_);
lean_ctor_set(v___x_1210_, 1, v_k_1060_);
lean_ctor_set(v___x_1210_, 0, v___x_1069_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_l_1158_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_l_1158_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_r_1206_);
lean_ctor_set(v___x_1065_, 3, v___x_1214_);
lean_ctor_set(v___x_1065_, 2, v_v_1208_);
lean_ctor_set(v___x_1065_, 1, v_k_1207_);
lean_ctor_set(v___x_1065_, 0, v___x_1212_);
v___x_1216_ = v___x_1065_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_k_1207_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_v_1208_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_r_1206_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_size_1223_; lean_object* v_k_1224_; lean_object* v_v_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v_size_1223_ = lean_ctor_get(v_r_1063_, 0);
v_k_1224_ = lean_ctor_get(v_r_1063_, 1);
v_v_1225_ = lean_ctor_get(v_r_1063_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; lean_object* v_unused_1238_; 
v_unused_1237_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1238_);
v___x_1227_ = v_r_1063_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_v_1225_);
lean_inc(v_k_1224_);
lean_inc(v_size_1223_);
lean_dec(v_r_1063_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 3, v_r_1206_);
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_size_1223_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_1224_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_1225_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_r_1206_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_r_1206_);
v___x_1230_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_unsigned_to_nat(2u);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1230_);
lean_ctor_set(v___x_1065_, 3, v_r_1206_);
lean_ctor_set(v___x_1065_, 0, v___x_1231_);
v___x_1233_ = v___x_1065_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_r_1206_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v___x_1230_);
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
}
else
{
lean_object* v___x_1240_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 3, v_r_1063_);
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1240_ = v___x_1065_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_r_1063_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_r_1063_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1065_);
lean_dec(v_v_1061_);
lean_dec(v_k_1060_);
if (lean_obj_tag(v_l_1062_) == 0)
{
if (lean_obj_tag(v_r_1063_) == 0)
{
lean_object* v_size_1242_; lean_object* v_k_1243_; lean_object* v_v_1244_; lean_object* v_l_1245_; lean_object* v_r_1246_; lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_l_1250_; lean_object* v_r_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_size_1242_ = lean_ctor_get(v_l_1062_, 0);
v_k_1243_ = lean_ctor_get(v_l_1062_, 1);
v_v_1244_ = lean_ctor_get(v_l_1062_, 2);
v_l_1245_ = lean_ctor_get(v_l_1062_, 3);
v_r_1246_ = lean_ctor_get(v_l_1062_, 4);
lean_inc(v_r_1246_);
v_size_1247_ = lean_ctor_get(v_r_1063_, 0);
v_k_1248_ = lean_ctor_get(v_r_1063_, 1);
v_v_1249_ = lean_ctor_get(v_r_1063_, 2);
v_l_1250_ = lean_ctor_get(v_r_1063_, 3);
lean_inc(v_l_1250_);
v_r_1251_ = lean_ctor_get(v_r_1063_, 4);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_dec_lt(v_size_1242_, v_size_1247_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1389_; 
lean_inc(v_l_1245_);
lean_inc(v_v_1244_);
lean_inc(v_k_1243_);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; lean_object* v_unused_1392_; lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1390_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_l_1062_, 2);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_l_1062_, 1);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_l_1062_, 0);
lean_dec(v_unused_1394_);
v___x_1255_ = v_l_1062_;
v_isShared_1256_ = v_isSharedCheck_1389_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v_l_1062_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1389_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v_tree_1258_; 
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1243_, v_v_1244_, v_l_1245_, v_r_1246_);
v_tree_1258_ = lean_ctor_get(v___x_1257_, 2);
lean_inc(v_tree_1258_);
if (lean_obj_tag(v_tree_1258_) == 0)
{
lean_object* v_k_1259_; lean_object* v_v_1260_; lean_object* v_size_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_k_1259_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_k_1259_);
v_v_1260_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_v_1260_);
lean_dec_ref(v___x_1257_);
v_size_1261_ = lean_ctor_get(v_tree_1258_, 0);
v___x_1262_ = lean_unsigned_to_nat(3u);
v___x_1263_ = lean_nat_mul(v___x_1262_, v_size_1261_);
v___x_1264_ = lean_nat_dec_lt(v___x_1263_, v_size_1247_);
lean_dec(v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
lean_dec(v_l_1250_);
v___x_1265_ = lean_nat_add(v___x_1252_, v_size_1261_);
v___x_1266_ = lean_nat_add(v___x_1265_, v_size_1247_);
lean_dec(v___x_1265_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_r_1063_);
lean_ctor_set(v___x_1255_, 3, v_tree_1258_);
lean_ctor_set(v___x_1255_, 2, v_v_1260_);
lean_ctor_set(v___x_1255_, 1, v_k_1259_);
lean_ctor_set(v___x_1255_, 0, v___x_1266_);
v___x_1268_ = v___x_1255_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_k_1259_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_v_1260_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_tree_1258_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v_r_1063_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
else
{
lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1324_; 
lean_inc(v_r_1251_);
lean_inc(v_v_1249_);
lean_inc(v_k_1248_);
lean_inc(v_size_1247_);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; lean_object* v_unused_1326_; lean_object* v_unused_1327_; lean_object* v_unused_1328_; lean_object* v_unused_1329_; 
v_unused_1325_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v_r_1063_, 2);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v_r_1063_, 1);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_r_1063_, 0);
lean_dec(v_unused_1329_);
v___x_1271_ = v_r_1063_;
v_isShared_1272_ = v_isSharedCheck_1324_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v_r_1063_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1324_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_size_1273_; lean_object* v_k_1274_; lean_object* v_v_1275_; lean_object* v_l_1276_; lean_object* v_r_1277_; lean_object* v_size_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_size_1273_ = lean_ctor_get(v_l_1250_, 0);
v_k_1274_ = lean_ctor_get(v_l_1250_, 1);
v_v_1275_ = lean_ctor_get(v_l_1250_, 2);
v_l_1276_ = lean_ctor_get(v_l_1250_, 3);
v_r_1277_ = lean_ctor_get(v_l_1250_, 4);
v_size_1278_ = lean_ctor_get(v_r_1251_, 0);
v___x_1279_ = lean_unsigned_to_nat(2u);
v___x_1280_ = lean_nat_mul(v___x_1279_, v_size_1278_);
v___x_1281_ = lean_nat_dec_lt(v_size_1273_, v___x_1280_);
lean_dec(v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1309_; 
lean_inc(v_r_1277_);
lean_inc(v_l_1276_);
lean_inc(v_v_1275_);
lean_inc(v_k_1274_);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_l_1250_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; 
v_unused_1310_ = lean_ctor_get(v_l_1250_, 4);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v_l_1250_, 3);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_l_1250_, 2);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_l_1250_, 1);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_l_1250_, 0);
lean_dec(v_unused_1314_);
v___x_1283_ = v_l_1250_;
v_isShared_1284_ = v_isSharedCheck_1309_;
goto v_resetjp_1282_;
}
else
{
lean_dec(v_l_1250_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1309_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1299_; 
v___x_1285_ = lean_nat_add(v___x_1252_, v_size_1261_);
v___x_1286_ = lean_nat_add(v___x_1285_, v_size_1247_);
lean_dec(v_size_1247_);
if (lean_obj_tag(v_l_1276_) == 0)
{
lean_object* v_size_1307_; 
v_size_1307_ = lean_ctor_get(v_l_1276_, 0);
lean_inc(v_size_1307_);
v___y_1299_ = v_size_1307_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___y_1299_ = v___x_1308_;
goto v___jp_1298_;
}
v___jp_1287_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_nat_add(v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec(v___y_1289_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 4, v_r_1251_);
lean_ctor_set(v___x_1283_, 3, v_r_1277_);
lean_ctor_set(v___x_1283_, 2, v_v_1249_);
lean_ctor_set(v___x_1283_, 1, v_k_1248_);
lean_ctor_set(v___x_1283_, 0, v___x_1291_);
v___x_1293_ = v___x_1283_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_r_1277_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v_r_1251_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 4, v___x_1293_);
lean_ctor_set(v___x_1271_, 3, v___y_1288_);
lean_ctor_set(v___x_1271_, 2, v_v_1275_);
lean_ctor_set(v___x_1271_, 1, v_k_1274_);
lean_ctor_set(v___x_1271_, 0, v___x_1286_);
v___x_1295_ = v___x_1271_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1274_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1275_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v___y_1288_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_nat_add(v___x_1285_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec(v___x_1285_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_l_1276_);
lean_ctor_set(v___x_1255_, 3, v_tree_1258_);
lean_ctor_set(v___x_1255_, 2, v_v_1260_);
lean_ctor_set(v___x_1255_, 1, v_k_1259_);
lean_ctor_set(v___x_1255_, 0, v___x_1300_);
v___x_1302_ = v___x_1255_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_k_1259_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_v_1260_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v_tree_1258_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v_l_1276_);
v___x_1302_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_nat_add(v___x_1252_, v_size_1278_);
if (lean_obj_tag(v_r_1277_) == 0)
{
lean_object* v_size_1304_; 
v_size_1304_ = lean_ctor_get(v_r_1277_, 0);
lean_inc(v_size_1304_);
v___y_1288_ = v___x_1302_;
v___y_1289_ = v___x_1303_;
v___y_1290_ = v_size_1304_;
goto v___jp_1287_;
}
else
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___y_1288_ = v___x_1302_;
v___y_1289_ = v___x_1303_;
v___y_1290_ = v___x_1305_;
goto v___jp_1287_;
}
}
}
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1315_ = lean_nat_add(v___x_1252_, v_size_1261_);
v___x_1316_ = lean_nat_add(v___x_1315_, v_size_1247_);
lean_dec(v_size_1247_);
v___x_1317_ = lean_nat_add(v___x_1315_, v_size_1273_);
lean_dec(v___x_1315_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 4, v_l_1250_);
lean_ctor_set(v___x_1271_, 3, v_tree_1258_);
lean_ctor_set(v___x_1271_, 2, v_v_1260_);
lean_ctor_set(v___x_1271_, 1, v_k_1259_);
lean_ctor_set(v___x_1271_, 0, v___x_1317_);
v___x_1319_ = v___x_1271_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_k_1259_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_v_1260_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_tree_1258_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_l_1250_);
v___x_1319_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_r_1251_);
lean_ctor_set(v___x_1255_, 3, v___x_1319_);
lean_ctor_set(v___x_1255_, 2, v_v_1249_);
lean_ctor_set(v___x_1255_, 1, v_k_1248_);
lean_ctor_set(v___x_1255_, 0, v___x_1316_);
v___x_1321_ = v___x_1255_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_r_1251_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
}
else
{
lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1383_; 
lean_inc(v_r_1251_);
lean_inc(v_v_1249_);
lean_inc(v_k_1248_);
lean_inc(v_size_1247_);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; lean_object* v_unused_1385_; lean_object* v_unused_1386_; lean_object* v_unused_1387_; lean_object* v_unused_1388_; 
v_unused_1384_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_r_1063_, 2);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_r_1063_, 1);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_r_1063_, 0);
lean_dec(v_unused_1388_);
v___x_1331_ = v_r_1063_;
v_isShared_1332_ = v_isSharedCheck_1383_;
goto v_resetjp_1330_;
}
else
{
lean_dec(v_r_1063_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1383_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
if (lean_obj_tag(v_l_1250_) == 0)
{
if (lean_obj_tag(v_r_1251_) == 0)
{
lean_object* v_k_1333_; lean_object* v_v_1334_; lean_object* v_size_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v_k_1333_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_k_1333_);
v_v_1334_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_v_1334_);
lean_dec_ref(v___x_1257_);
v_size_1335_ = lean_ctor_get(v_l_1250_, 0);
v___x_1336_ = lean_nat_add(v___x_1252_, v_size_1247_);
lean_dec(v_size_1247_);
v___x_1337_ = lean_nat_add(v___x_1252_, v_size_1335_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 4, v_l_1250_);
lean_ctor_set(v___x_1331_, 3, v_tree_1258_);
lean_ctor_set(v___x_1331_, 2, v_v_1334_);
lean_ctor_set(v___x_1331_, 1, v_k_1333_);
lean_ctor_set(v___x_1331_, 0, v___x_1337_);
v___x_1339_ = v___x_1331_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1333_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1334_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_tree_1258_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_l_1250_);
v___x_1339_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1341_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_r_1251_);
lean_ctor_set(v___x_1255_, 3, v___x_1339_);
lean_ctor_set(v___x_1255_, 2, v_v_1249_);
lean_ctor_set(v___x_1255_, 1, v_k_1248_);
lean_ctor_set(v___x_1255_, 0, v___x_1336_);
v___x_1341_ = v___x_1255_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_r_1251_);
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
lean_object* v_k_1344_; lean_object* v_v_1345_; lean_object* v_k_1346_; lean_object* v_v_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_size_1247_);
v_k_1344_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_k_1344_);
v_v_1345_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_v_1345_);
lean_dec_ref(v___x_1257_);
v_k_1346_ = lean_ctor_get(v_l_1250_, 1);
v_v_1347_ = lean_ctor_get(v_l_1250_, 2);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_l_1250_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; lean_object* v_unused_1363_; lean_object* v_unused_1364_; 
v_unused_1362_ = lean_ctor_get(v_l_1250_, 4);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_l_1250_, 3);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_l_1250_, 0);
lean_dec(v_unused_1364_);
v___x_1349_ = v_l_1250_;
v_isShared_1350_ = v_isSharedCheck_1361_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_v_1347_);
lean_inc(v_k_1346_);
lean_dec(v_l_1250_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1361_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_unsigned_to_nat(3u);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 4, v_r_1251_);
lean_ctor_set(v___x_1349_, 3, v_r_1251_);
lean_ctor_set(v___x_1349_, 2, v_v_1345_);
lean_ctor_set(v___x_1349_, 1, v_k_1344_);
lean_ctor_set(v___x_1349_, 0, v___x_1252_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_k_1344_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_v_1345_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_r_1251_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_r_1251_);
v___x_1353_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 3, v_r_1251_);
lean_ctor_set(v___x_1331_, 0, v___x_1252_);
v___x_1355_ = v___x_1331_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_r_1251_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v_r_1251_);
v___x_1355_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1357_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1355_);
lean_ctor_set(v___x_1255_, 3, v___x_1353_);
lean_ctor_set(v___x_1255_, 2, v_v_1347_);
lean_ctor_set(v___x_1255_, 1, v_k_1346_);
lean_ctor_set(v___x_1255_, 0, v___x_1351_);
v___x_1357_ = v___x_1255_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_k_1346_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_v_1347_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1251_) == 0)
{
lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_dec(v_size_1247_);
v_k_1365_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_k_1365_);
v_v_1366_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_v_1366_);
lean_dec_ref(v___x_1257_);
v___x_1367_ = lean_unsigned_to_nat(3u);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 4, v_l_1250_);
lean_ctor_set(v___x_1331_, 2, v_v_1366_);
lean_ctor_set(v___x_1331_, 1, v_k_1365_);
lean_ctor_set(v___x_1331_, 0, v___x_1252_);
v___x_1369_ = v___x_1331_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1365_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1366_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_l_1250_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_l_1250_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1371_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v_r_1251_);
lean_ctor_set(v___x_1255_, 3, v___x_1369_);
lean_ctor_set(v___x_1255_, 2, v_v_1249_);
lean_ctor_set(v___x_1255_, 1, v_k_1248_);
lean_ctor_set(v___x_1255_, 0, v___x_1367_);
v___x_1371_ = v___x_1255_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_r_1251_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_object* v_k_1374_; lean_object* v_v_1375_; lean_object* v___x_1377_; 
v_k_1374_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_k_1374_);
v_v_1375_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_v_1375_);
lean_dec_ref(v___x_1257_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 3, v_r_1251_);
v___x_1377_ = v___x_1331_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_size_1247_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_r_1251_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_r_1251_);
v___x_1377_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1378_ = lean_unsigned_to_nat(2u);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___x_1377_);
lean_ctor_set(v___x_1255_, 3, v_r_1251_);
lean_ctor_set(v___x_1255_, 2, v_v_1375_);
lean_ctor_set(v___x_1255_, 1, v_k_1374_);
lean_ctor_set(v___x_1255_, 0, v___x_1378_);
v___x_1380_ = v___x_1255_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1381_, 3, v_r_1251_);
lean_ctor_set(v_reuseFailAlloc_1381_, 4, v___x_1377_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
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
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1547_; 
lean_inc(v_r_1251_);
lean_inc(v_v_1249_);
lean_inc(v_k_1248_);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_r_1063_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1548_ = lean_ctor_get(v_r_1063_, 4);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1063_, 3);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_r_1063_, 2);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_r_1063_, 1);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_r_1063_, 0);
lean_dec(v_unused_1552_);
v___x_1396_ = v_r_1063_;
v_isShared_1397_ = v_isSharedCheck_1547_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v_r_1063_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1547_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v_tree_1399_; 
v___x_1398_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1248_, v_v_1249_, v_l_1250_, v_r_1251_);
v_tree_1399_ = lean_ctor_get(v___x_1398_, 2);
lean_inc(v_tree_1399_);
if (lean_obj_tag(v_tree_1399_) == 0)
{
lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v_size_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_k_1400_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_k_1400_);
v_v_1401_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_v_1401_);
lean_dec_ref(v___x_1398_);
v_size_1402_ = lean_ctor_get(v_tree_1399_, 0);
v___x_1403_ = lean_unsigned_to_nat(3u);
v___x_1404_ = lean_nat_mul(v___x_1403_, v_size_1402_);
v___x_1405_ = lean_nat_dec_lt(v___x_1404_, v_size_1242_);
lean_dec(v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_r_1246_);
v___x_1406_ = lean_nat_add(v___x_1252_, v_size_1242_);
v___x_1407_ = lean_nat_add(v___x_1406_, v_size_1402_);
lean_dec(v___x_1406_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_tree_1399_);
lean_ctor_set(v___x_1396_, 3, v_l_1062_);
lean_ctor_set(v___x_1396_, 2, v_v_1401_);
lean_ctor_set(v___x_1396_, 1, v_k_1400_);
lean_ctor_set(v___x_1396_, 0, v___x_1407_);
v___x_1409_ = v___x_1396_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_l_1062_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_tree_1399_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1476_; 
lean_inc(v_l_1245_);
lean_inc(v_v_1244_);
lean_inc(v_k_1243_);
lean_inc(v_size_1242_);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1477_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_l_1062_, 2);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_l_1062_, 1);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_l_1062_, 0);
lean_dec(v_unused_1481_);
v___x_1412_ = v_l_1062_;
v_isShared_1413_ = v_isSharedCheck_1476_;
goto v_resetjp_1411_;
}
else
{
lean_dec(v_l_1062_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1476_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_size_1414_; lean_object* v_size_1415_; lean_object* v_k_1416_; lean_object* v_v_1417_; lean_object* v_l_1418_; lean_object* v_r_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_size_1414_ = lean_ctor_get(v_l_1245_, 0);
v_size_1415_ = lean_ctor_get(v_r_1246_, 0);
v_k_1416_ = lean_ctor_get(v_r_1246_, 1);
v_v_1417_ = lean_ctor_get(v_r_1246_, 2);
v_l_1418_ = lean_ctor_get(v_r_1246_, 3);
v_r_1419_ = lean_ctor_get(v_r_1246_, 4);
v___x_1420_ = lean_unsigned_to_nat(2u);
v___x_1421_ = lean_nat_mul(v___x_1420_, v_size_1414_);
v___x_1422_ = lean_nat_dec_lt(v_size_1415_, v___x_1421_);
lean_dec(v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1460_; 
lean_inc(v_r_1419_);
lean_inc(v_l_1418_);
lean_inc(v_v_1417_);
lean_inc(v_k_1416_);
lean_del_object(v___x_1412_);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_r_1246_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; lean_object* v_unused_1464_; lean_object* v_unused_1465_; 
v_unused_1461_ = lean_ctor_get(v_r_1246_, 4);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_r_1246_, 3);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_r_1246_, 2);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_r_1246_, 1);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_r_1246_, 0);
lean_dec(v_unused_1465_);
v___x_1424_ = v_r_1246_;
v_isShared_1425_ = v_isSharedCheck_1460_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v_r_1246_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1460_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___x_1448_; lean_object* v___y_1450_; 
v___x_1426_ = lean_nat_add(v___x_1252_, v_size_1242_);
lean_dec(v_size_1242_);
v___x_1427_ = lean_nat_add(v___x_1426_, v_size_1402_);
lean_dec(v___x_1426_);
v___x_1448_ = lean_nat_add(v___x_1252_, v_size_1414_);
if (lean_obj_tag(v_l_1418_) == 0)
{
lean_object* v_size_1458_; 
v_size_1458_ = lean_ctor_get(v_l_1418_, 0);
lean_inc(v_size_1458_);
v___y_1450_ = v_size_1458_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_unsigned_to_nat(0u);
v___y_1450_ = v___x_1459_;
goto v___jp_1449_;
}
v___jp_1428_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_nat_add(v___y_1429_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec(v___y_1429_);
lean_inc_ref(v_tree_1399_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_tree_1399_);
lean_ctor_set(v___x_1424_, 3, v_r_1419_);
lean_ctor_set(v___x_1424_, 2, v_v_1401_);
lean_ctor_set(v___x_1424_, 1, v_k_1400_);
lean_ctor_set(v___x_1424_, 0, v___x_1432_);
v___x_1434_ = v___x_1424_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_r_1419_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_tree_1399_);
v___x_1434_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_isSharedCheck_1441_ = !lean_is_exclusive(v_tree_1399_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; lean_object* v_unused_1446_; 
v_unused_1442_ = lean_ctor_get(v_tree_1399_, 4);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_tree_1399_, 3);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_tree_1399_, 2);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_tree_1399_, 1);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_tree_1399_, 0);
lean_dec(v_unused_1446_);
v___x_1436_ = v_tree_1399_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v_tree_1399_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 4, v___x_1434_);
lean_ctor_set(v___x_1436_, 3, v___y_1430_);
lean_ctor_set(v___x_1436_, 2, v_v_1417_);
lean_ctor_set(v___x_1436_, 1, v_k_1416_);
lean_ctor_set(v___x_1436_, 0, v___x_1427_);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_k_1416_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_v_1417_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v___y_1430_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v___x_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
v___jp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_nat_add(v___x_1448_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec(v___x_1448_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_l_1418_);
lean_ctor_set(v___x_1396_, 3, v_l_1245_);
lean_ctor_set(v___x_1396_, 2, v_v_1244_);
lean_ctor_set(v___x_1396_, 1, v_k_1243_);
lean_ctor_set(v___x_1396_, 0, v___x_1451_);
v___x_1453_ = v___x_1396_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_l_1245_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_l_1418_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_nat_add(v___x_1252_, v_size_1402_);
if (lean_obj_tag(v_r_1419_) == 0)
{
lean_object* v_size_1455_; 
v_size_1455_ = lean_ctor_get(v_r_1419_, 0);
lean_inc(v_size_1455_);
v___y_1429_ = v___x_1454_;
v___y_1430_ = v___x_1453_;
v___y_1431_ = v_size_1455_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
v___y_1429_ = v___x_1454_;
v___y_1430_ = v___x_1453_;
v___y_1431_ = v___x_1456_;
goto v___jp_1428_;
}
}
}
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1466_ = lean_nat_add(v___x_1252_, v_size_1242_);
lean_dec(v_size_1242_);
v___x_1467_ = lean_nat_add(v___x_1466_, v_size_1402_);
lean_dec(v___x_1466_);
v___x_1468_ = lean_nat_add(v___x_1252_, v_size_1402_);
v___x_1469_ = lean_nat_add(v___x_1468_, v_size_1415_);
lean_dec(v___x_1468_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_tree_1399_);
lean_ctor_set(v___x_1396_, 3, v_r_1246_);
lean_ctor_set(v___x_1396_, 2, v_v_1401_);
lean_ctor_set(v___x_1396_, 1, v_k_1400_);
lean_ctor_set(v___x_1396_, 0, v___x_1469_);
v___x_1471_ = v___x_1396_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_r_1246_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_tree_1399_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v___x_1471_);
lean_ctor_set(v___x_1412_, 0, v___x_1467_);
v___x_1473_ = v___x_1412_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_l_1245_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1245_) == 0)
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1505_; 
lean_inc_ref(v_l_1245_);
lean_inc(v_v_1244_);
lean_inc(v_k_1243_);
lean_inc(v_size_1242_);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1506_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_l_1062_, 2);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_l_1062_, 1);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_l_1062_, 0);
lean_dec(v_unused_1510_);
v___x_1483_ = v_l_1062_;
v_isShared_1484_ = v_isSharedCheck_1505_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v_l_1062_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1505_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
if (lean_obj_tag(v_r_1246_) == 0)
{
lean_object* v_k_1485_; lean_object* v_v_1486_; lean_object* v_size_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v_k_1485_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_k_1485_);
v_v_1486_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_v_1486_);
lean_dec_ref(v___x_1398_);
v_size_1487_ = lean_ctor_get(v_r_1246_, 0);
v___x_1488_ = lean_nat_add(v___x_1252_, v_size_1242_);
lean_dec(v_size_1242_);
v___x_1489_ = lean_nat_add(v___x_1252_, v_size_1487_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_tree_1399_);
lean_ctor_set(v___x_1396_, 3, v_r_1246_);
lean_ctor_set(v___x_1396_, 2, v_v_1486_);
lean_ctor_set(v___x_1396_, 1, v_k_1485_);
lean_ctor_set(v___x_1396_, 0, v___x_1489_);
v___x_1491_ = v___x_1396_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_r_1246_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_tree_1399_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v___x_1491_);
lean_ctor_set(v___x_1483_, 0, v___x_1488_);
v___x_1493_ = v___x_1483_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_l_1245_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_dec(v_size_1242_);
v_k_1496_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_k_1496_);
v_v_1497_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_v_1497_);
lean_dec_ref(v___x_1398_);
v___x_1498_ = lean_unsigned_to_nat(3u);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_r_1246_);
lean_ctor_set(v___x_1396_, 3, v_r_1246_);
lean_ctor_set(v___x_1396_, 2, v_v_1497_);
lean_ctor_set(v___x_1396_, 1, v_k_1496_);
lean_ctor_set(v___x_1396_, 0, v___x_1252_);
v___x_1500_ = v___x_1396_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1496_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1497_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_r_1246_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_r_1246_);
v___x_1500_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v___x_1500_);
lean_ctor_set(v___x_1483_, 0, v___x_1498_);
v___x_1502_ = v___x_1483_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_l_1245_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1246_) == 0)
{
lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1535_; 
lean_inc(v_l_1245_);
lean_inc(v_v_1244_);
lean_inc(v_k_1243_);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1536_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_l_1062_, 2);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_l_1062_, 1);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_l_1062_, 0);
lean_dec(v_unused_1540_);
v___x_1512_ = v_l_1062_;
v_isShared_1513_ = v_isSharedCheck_1535_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v_l_1062_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1535_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_k_1514_; lean_object* v_v_1515_; lean_object* v_k_1516_; lean_object* v_v_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1531_; 
v_k_1514_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_k_1514_);
v_v_1515_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_v_1515_);
lean_dec_ref(v___x_1398_);
v_k_1516_ = lean_ctor_get(v_r_1246_, 1);
v_v_1517_ = lean_ctor_get(v_r_1246_, 2);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_r_1246_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1532_ = lean_ctor_get(v_r_1246_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_r_1246_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_r_1246_, 0);
lean_dec(v_unused_1534_);
v___x_1519_ = v_r_1246_;
v_isShared_1520_ = v_isSharedCheck_1531_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_v_1517_);
lean_inc(v_k_1516_);
lean_dec(v_r_1246_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1531_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_unsigned_to_nat(3u);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 4, v_l_1245_);
lean_ctor_set(v___x_1519_, 3, v_l_1245_);
lean_ctor_set(v___x_1519_, 2, v_v_1244_);
lean_ctor_set(v___x_1519_, 1, v_k_1243_);
lean_ctor_set(v___x_1519_, 0, v___x_1252_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1243_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1244_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_l_1245_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_l_1245_);
v___x_1523_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_l_1245_);
lean_ctor_set(v___x_1396_, 3, v_l_1245_);
lean_ctor_set(v___x_1396_, 2, v_v_1515_);
lean_ctor_set(v___x_1396_, 1, v_k_1514_);
lean_ctor_set(v___x_1396_, 0, v___x_1252_);
v___x_1525_ = v___x_1396_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1515_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_l_1245_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_l_1245_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 4, v___x_1525_);
lean_ctor_set(v___x_1512_, 3, v___x_1523_);
lean_ctor_set(v___x_1512_, 2, v_v_1517_);
lean_ctor_set(v___x_1512_, 1, v_k_1516_);
lean_ctor_set(v___x_1512_, 0, v___x_1521_);
v___x_1527_ = v___x_1512_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
else
{
lean_object* v_k_1541_; lean_object* v_v_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v_k_1541_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_k_1541_);
v_v_1542_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_v_1542_);
lean_dec_ref(v___x_1398_);
v___x_1543_ = lean_unsigned_to_nat(2u);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_r_1246_);
lean_ctor_set(v___x_1396_, 3, v_l_1062_);
lean_ctor_set(v___x_1396_, 2, v_v_1542_);
lean_ctor_set(v___x_1396_, 1, v_k_1541_);
lean_ctor_set(v___x_1396_, 0, v___x_1543_);
v___x_1545_ = v___x_1396_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1542_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_l_1062_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_r_1246_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
}
}
else
{
return v_l_1062_;
}
}
else
{
return v_r_1063_;
}
}
default: 
{
lean_object* v_impl_1553_; lean_object* v___x_1554_; 
v_impl_1553_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1058_, v_r_1063_);
v___x_1554_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1553_) == 0)
{
if (lean_obj_tag(v_l_1062_) == 0)
{
lean_object* v_size_1555_; lean_object* v_size_1556_; lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v_l_1559_; lean_object* v_r_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_size_1555_ = lean_ctor_get(v_impl_1553_, 0);
lean_inc(v_size_1555_);
v_size_1556_ = lean_ctor_get(v_l_1062_, 0);
v_k_1557_ = lean_ctor_get(v_l_1062_, 1);
v_v_1558_ = lean_ctor_get(v_l_1062_, 2);
v_l_1559_ = lean_ctor_get(v_l_1062_, 3);
v_r_1560_ = lean_ctor_get(v_l_1062_, 4);
lean_inc(v_r_1560_);
v___x_1561_ = lean_unsigned_to_nat(3u);
v___x_1562_ = lean_nat_mul(v___x_1561_, v_size_1555_);
v___x_1563_ = lean_nat_dec_lt(v___x_1562_, v_size_1556_);
lean_dec(v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_dec(v_r_1560_);
v___x_1564_ = lean_nat_add(v___x_1554_, v_size_1556_);
v___x_1565_ = lean_nat_add(v___x_1564_, v_size_1555_);
lean_dec(v_size_1555_);
lean_dec(v___x_1564_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_impl_1553_);
lean_ctor_set(v___x_1065_, 0, v___x_1565_);
v___x_1567_ = v___x_1065_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v_l_1062_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v_impl_1553_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
else
{
lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1634_; 
lean_inc(v_l_1559_);
lean_inc(v_v_1558_);
lean_inc(v_k_1557_);
lean_inc(v_size_1556_);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; 
v_unused_1635_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_l_1062_, 2);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_l_1062_, 1);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_l_1062_, 0);
lean_dec(v_unused_1639_);
v___x_1570_ = v_l_1062_;
v_isShared_1571_ = v_isSharedCheck_1634_;
goto v_resetjp_1569_;
}
else
{
lean_dec(v_l_1062_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1634_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_size_1572_; lean_object* v_size_1573_; lean_object* v_k_1574_; lean_object* v_v_1575_; lean_object* v_l_1576_; lean_object* v_r_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v_size_1572_ = lean_ctor_get(v_l_1559_, 0);
v_size_1573_ = lean_ctor_get(v_r_1560_, 0);
v_k_1574_ = lean_ctor_get(v_r_1560_, 1);
v_v_1575_ = lean_ctor_get(v_r_1560_, 2);
v_l_1576_ = lean_ctor_get(v_r_1560_, 3);
v_r_1577_ = lean_ctor_get(v_r_1560_, 4);
v___x_1578_ = lean_unsigned_to_nat(2u);
v___x_1579_ = lean_nat_mul(v___x_1578_, v_size_1572_);
v___x_1580_ = lean_nat_dec_lt(v_size_1573_, v___x_1579_);
lean_dec(v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1609_; 
lean_inc(v_r_1577_);
lean_inc(v_l_1576_);
lean_inc(v_v_1575_);
lean_inc(v_k_1574_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_r_1560_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1610_ = lean_ctor_get(v_r_1560_, 4);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_r_1560_, 3);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_r_1560_, 2);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_r_1560_, 1);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_r_1560_, 0);
lean_dec(v_unused_1614_);
v___x_1582_ = v_r_1560_;
v_isShared_1583_ = v_isSharedCheck_1609_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_r_1560_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1609_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___x_1597_; lean_object* v___y_1599_; 
v___x_1584_ = lean_nat_add(v___x_1554_, v_size_1556_);
lean_dec(v_size_1556_);
v___x_1585_ = lean_nat_add(v___x_1584_, v_size_1555_);
lean_dec(v___x_1584_);
v___x_1597_ = lean_nat_add(v___x_1554_, v_size_1572_);
if (lean_obj_tag(v_l_1576_) == 0)
{
lean_object* v_size_1607_; 
v_size_1607_ = lean_ctor_get(v_l_1576_, 0);
lean_inc(v_size_1607_);
v___y_1599_ = v_size_1607_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___y_1599_ = v___x_1608_;
goto v___jp_1598_;
}
v___jp_1586_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = lean_nat_add(v___y_1587_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec(v___y_1587_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v_impl_1553_);
lean_ctor_set(v___x_1582_, 3, v_r_1577_);
lean_ctor_set(v___x_1582_, 2, v_v_1061_);
lean_ctor_set(v___x_1582_, 1, v_k_1060_);
lean_ctor_set(v___x_1582_, 0, v___x_1590_);
v___x_1592_ = v___x_1582_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_r_1577_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_impl_1553_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 4, v___x_1592_);
lean_ctor_set(v___x_1570_, 3, v___y_1588_);
lean_ctor_set(v___x_1570_, 2, v_v_1575_);
lean_ctor_set(v___x_1570_, 1, v_k_1574_);
lean_ctor_set(v___x_1570_, 0, v___x_1585_);
v___x_1594_ = v___x_1570_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1574_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1575_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v___y_1588_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
v___jp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_nat_add(v___x_1597_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec(v___x_1597_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_l_1576_);
lean_ctor_set(v___x_1065_, 3, v_l_1559_);
lean_ctor_set(v___x_1065_, 2, v_v_1558_);
lean_ctor_set(v___x_1065_, 1, v_k_1557_);
lean_ctor_set(v___x_1065_, 0, v___x_1600_);
v___x_1602_ = v___x_1065_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_k_1557_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_v_1558_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_l_1559_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_l_1576_);
v___x_1602_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_nat_add(v___x_1554_, v_size_1555_);
lean_dec(v_size_1555_);
if (lean_obj_tag(v_r_1577_) == 0)
{
lean_object* v_size_1604_; 
v_size_1604_ = lean_ctor_get(v_r_1577_, 0);
lean_inc(v_size_1604_);
v___y_1587_ = v___x_1603_;
v___y_1588_ = v___x_1602_;
v___y_1589_ = v_size_1604_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v___y_1587_ = v___x_1603_;
v___y_1588_ = v___x_1602_;
v___y_1589_ = v___x_1605_;
goto v___jp_1586_;
}
}
}
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
lean_del_object(v___x_1065_);
v___x_1615_ = lean_nat_add(v___x_1554_, v_size_1556_);
lean_dec(v_size_1556_);
v___x_1616_ = lean_nat_add(v___x_1615_, v_size_1555_);
lean_dec(v___x_1615_);
v___x_1617_ = lean_nat_add(v___x_1554_, v_size_1555_);
lean_dec(v_size_1555_);
v___x_1618_ = lean_nat_add(v___x_1617_, v_size_1573_);
lean_dec(v___x_1617_);
lean_inc_ref(v_impl_1553_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 4, v_impl_1553_);
lean_ctor_set(v___x_1570_, 3, v_r_1560_);
lean_ctor_set(v___x_1570_, 2, v_v_1061_);
lean_ctor_set(v___x_1570_, 1, v_k_1060_);
lean_ctor_set(v___x_1570_, 0, v___x_1618_);
v___x_1620_ = v___x_1570_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v_r_1560_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v_impl_1553_);
v___x_1620_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_isSharedCheck_1627_ = !lean_is_exclusive(v_impl_1553_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; lean_object* v_unused_1629_; lean_object* v_unused_1630_; lean_object* v_unused_1631_; lean_object* v_unused_1632_; 
v_unused_1628_ = lean_ctor_get(v_impl_1553_, 4);
lean_dec(v_unused_1628_);
v_unused_1629_ = lean_ctor_get(v_impl_1553_, 3);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_impl_1553_, 2);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_impl_1553_, 1);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_impl_1553_, 0);
lean_dec(v_unused_1632_);
v___x_1622_ = v_impl_1553_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_impl_1553_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v___x_1620_);
lean_ctor_set(v___x_1622_, 3, v_l_1559_);
lean_ctor_set(v___x_1622_, 2, v_v_1558_);
lean_ctor_set(v___x_1622_, 1, v_k_1557_);
lean_ctor_set(v___x_1622_, 0, v___x_1616_);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_k_1557_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_v_1558_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_l_1559_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v___x_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v_size_1640_ = lean_ctor_get(v_impl_1553_, 0);
lean_inc(v_size_1640_);
v___x_1641_ = lean_nat_add(v___x_1554_, v_size_1640_);
lean_dec(v_size_1640_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_impl_1553_);
lean_ctor_set(v___x_1065_, 0, v___x_1641_);
v___x_1643_ = v___x_1065_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_l_1062_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_impl_1553_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
else
{
if (lean_obj_tag(v_l_1062_) == 0)
{
lean_object* v_l_1645_; 
v_l_1645_ = lean_ctor_get(v_l_1062_, 3);
if (lean_obj_tag(v_l_1645_) == 0)
{
lean_object* v_r_1646_; 
lean_inc_ref(v_l_1645_);
v_r_1646_ = lean_ctor_get(v_l_1062_, 4);
lean_inc(v_r_1646_);
if (lean_obj_tag(v_r_1646_) == 0)
{
lean_object* v_size_1647_; lean_object* v_k_1648_; lean_object* v_v_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1662_; 
v_size_1647_ = lean_ctor_get(v_l_1062_, 0);
v_k_1648_ = lean_ctor_get(v_l_1062_, 1);
v_v_1649_ = lean_ctor_get(v_l_1062_, 2);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; lean_object* v_unused_1664_; 
v_unused_1663_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1664_);
v___x_1651_ = v_l_1062_;
v_isShared_1652_ = v_isSharedCheck_1662_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_v_1649_);
lean_inc(v_k_1648_);
lean_inc(v_size_1647_);
lean_dec(v_l_1062_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1662_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v_size_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v_size_1653_ = lean_ctor_get(v_r_1646_, 0);
v___x_1654_ = lean_nat_add(v___x_1554_, v_size_1647_);
lean_dec(v_size_1647_);
v___x_1655_ = lean_nat_add(v___x_1554_, v_size_1653_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 4, v_impl_1553_);
lean_ctor_set(v___x_1651_, 3, v_r_1646_);
lean_ctor_set(v___x_1651_, 2, v_v_1061_);
lean_ctor_set(v___x_1651_, 1, v_k_1060_);
lean_ctor_set(v___x_1651_, 0, v___x_1655_);
v___x_1657_ = v___x_1651_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_r_1646_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_impl_1553_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1657_);
lean_ctor_set(v___x_1065_, 3, v_l_1645_);
lean_ctor_set(v___x_1065_, 2, v_v_1649_);
lean_ctor_set(v___x_1065_, 1, v_k_1648_);
lean_ctor_set(v___x_1065_, 0, v___x_1654_);
v___x_1659_ = v___x_1065_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1648_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1649_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_l_1645_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_k_1665_; lean_object* v_v_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1677_; 
v_k_1665_ = lean_ctor_get(v_l_1062_, 1);
v_v_1666_ = lean_ctor_get(v_l_1062_, 2);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; 
v_unused_1678_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1062_, 0);
lean_dec(v_unused_1680_);
v___x_1668_ = v_l_1062_;
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_v_1666_);
lean_inc(v_k_1665_);
lean_dec(v_l_1062_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1677_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = lean_unsigned_to_nat(3u);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 3, v_r_1646_);
lean_ctor_set(v___x_1668_, 2, v_v_1061_);
lean_ctor_set(v___x_1668_, 1, v_k_1060_);
lean_ctor_set(v___x_1668_, 0, v___x_1554_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_r_1646_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v_r_1646_);
v___x_1672_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1672_);
lean_ctor_set(v___x_1065_, 3, v_l_1645_);
lean_ctor_set(v___x_1065_, 2, v_v_1666_);
lean_ctor_set(v___x_1065_, 1, v_k_1665_);
lean_ctor_set(v___x_1065_, 0, v___x_1670_);
v___x_1674_ = v___x_1065_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_k_1665_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_v_1666_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_l_1645_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_object* v_r_1681_; 
v_r_1681_ = lean_ctor_get(v_l_1062_, 4);
lean_inc(v_r_1681_);
if (lean_obj_tag(v_r_1681_) == 0)
{
lean_object* v_k_1682_; lean_object* v_v_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1706_; 
lean_inc(v_l_1645_);
v_k_1682_ = lean_ctor_get(v_l_1062_, 1);
v_v_1683_ = lean_ctor_get(v_l_1062_, 2);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_l_1062_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1707_ = lean_ctor_get(v_l_1062_, 4);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_l_1062_, 3);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_l_1062_, 0);
lean_dec(v_unused_1709_);
v___x_1685_ = v_l_1062_;
v_isShared_1686_ = v_isSharedCheck_1706_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_v_1683_);
lean_inc(v_k_1682_);
lean_dec(v_l_1062_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1706_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_k_1687_; lean_object* v_v_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1702_; 
v_k_1687_ = lean_ctor_get(v_r_1681_, 1);
v_v_1688_ = lean_ctor_get(v_r_1681_, 2);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_r_1681_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; 
v_unused_1703_ = lean_ctor_get(v_r_1681_, 4);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_r_1681_, 3);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_r_1681_, 0);
lean_dec(v_unused_1705_);
v___x_1690_ = v_r_1681_;
v_isShared_1691_ = v_isSharedCheck_1702_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_v_1688_);
lean_inc(v_k_1687_);
lean_dec(v_r_1681_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1702_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_unsigned_to_nat(3u);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 4, v_l_1645_);
lean_ctor_set(v___x_1690_, 3, v_l_1645_);
lean_ctor_set(v___x_1690_, 2, v_v_1683_);
lean_ctor_set(v___x_1690_, 1, v_k_1682_);
lean_ctor_set(v___x_1690_, 0, v___x_1554_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1682_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1683_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_l_1645_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v_l_1645_);
v___x_1694_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 4, v_l_1645_);
lean_ctor_set(v___x_1685_, 2, v_v_1061_);
lean_ctor_set(v___x_1685_, 1, v_k_1060_);
lean_ctor_set(v___x_1685_, 0, v___x_1554_);
v___x_1696_ = v___x_1685_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_l_1645_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_l_1645_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v___x_1696_);
lean_ctor_set(v___x_1065_, 3, v___x_1694_);
lean_ctor_set(v___x_1065_, 2, v_v_1688_);
lean_ctor_set(v___x_1065_, 1, v_k_1687_);
lean_ctor_set(v___x_1065_, 0, v___x_1692_);
v___x_1698_ = v___x_1065_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1687_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1688_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_unsigned_to_nat(2u);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_r_1681_);
lean_ctor_set(v___x_1065_, 0, v___x_1710_);
v___x_1712_ = v___x_1065_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_l_1062_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_r_1681_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v___x_1715_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_l_1062_);
lean_ctor_set(v___x_1065_, 0, v___x_1554_);
v___x_1715_ = v___x_1065_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_k_1060_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_v_1061_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_l_1062_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v_l_1062_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
}
else
{
return v_t_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1719_, lean_object* v_t_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1719_, v_t_1720_);
lean_dec(v_k_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1722_, lean_object* v_declName_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v_ext_1729_; lean_object* v_toEnvExtension_1730_; lean_object* v_env_1731_; lean_object* v_asyncMode_1732_; lean_object* v___x_1733_; lean_object* v___y_1735_; lean_object* v_funCC_1762_; uint8_t v___x_1763_; 
v___x_1727_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1728_ = lean_st_ref_get(v_a_1725_);
v_ext_1729_ = lean_ctor_get(v_ext_1722_, 1);
v_toEnvExtension_1730_ = lean_ctor_get(v_ext_1729_, 0);
v_env_1731_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref(v_env_1731_);
lean_dec(v___x_1728_);
v_asyncMode_1732_ = lean_ctor_get(v_toEnvExtension_1730_, 2);
v___x_1733_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1727_, v_ext_1722_, v_env_1731_, v_asyncMode_1732_);
v_funCC_1762_ = lean_ctor_get(v___x_1733_, 2);
lean_inc(v_funCC_1762_);
v___x_1763_ = l_Lean_NameSet_contains(v_funCC_1762_, v_declName_1723_);
lean_dec(v_funCC_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_inc(v_declName_1723_);
v___x_1764_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_dec_ref_known(v___x_1764_, 1);
v___y_1735_ = v_a_1725_;
goto v___jp_1734_;
}
else
{
lean_dec(v___x_1733_);
lean_dec(v_declName_1723_);
lean_dec_ref(v_ext_1722_);
return v___x_1764_;
}
}
else
{
v___y_1735_ = v_a_1725_;
goto v___jp_1734_;
}
v___jp_1734_:
{
lean_object* v_funCC_1736_; lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___x_1739_; lean_object* v_env_1740_; lean_object* v_nextMacroScope_1741_; lean_object* v_ngen_1742_; lean_object* v_auxDeclNGen_1743_; lean_object* v_traceState_1744_; lean_object* v_recordedDeps_1745_; lean_object* v_messages_1746_; lean_object* v_infoState_1747_; lean_object* v_snapshotTasks_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1760_; 
v_funCC_1736_ = lean_ctor_get(v___x_1733_, 2);
lean_inc(v_funCC_1736_);
lean_dec(v___x_1733_);
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1723_, v_funCC_1736_);
lean_dec(v_declName_1723_);
v___f_1738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1738_, 0, v___x_1737_);
v___x_1739_ = lean_st_ref_take(v___y_1735_);
v_env_1740_ = lean_ctor_get(v___x_1739_, 0);
v_nextMacroScope_1741_ = lean_ctor_get(v___x_1739_, 1);
v_ngen_1742_ = lean_ctor_get(v___x_1739_, 2);
v_auxDeclNGen_1743_ = lean_ctor_get(v___x_1739_, 3);
v_traceState_1744_ = lean_ctor_get(v___x_1739_, 4);
v_recordedDeps_1745_ = lean_ctor_get(v___x_1739_, 6);
v_messages_1746_ = lean_ctor_get(v___x_1739_, 7);
v_infoState_1747_ = lean_ctor_get(v___x_1739_, 8);
v_snapshotTasks_1748_ = lean_ctor_get(v___x_1739_, 9);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1739_, 5);
lean_dec(v_unused_1761_);
v___x_1750_ = v___x_1739_;
v_isShared_1751_ = v_isSharedCheck_1760_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snapshotTasks_1748_);
lean_inc(v_infoState_1747_);
lean_inc(v_messages_1746_);
lean_inc(v_recordedDeps_1745_);
lean_inc(v_traceState_1744_);
lean_inc(v_auxDeclNGen_1743_);
lean_inc(v_ngen_1742_);
lean_inc(v_nextMacroScope_1741_);
lean_inc(v_env_1740_);
lean_dec(v___x_1739_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1760_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1752_ = lean_box(0);
v___x_1753_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1722_, v_env_1740_, v___f_1738_);
v___x_1754_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 5, v___x_1754_);
lean_ctor_set(v___x_1750_, 0, v___x_1753_);
v___x_1756_ = v___x_1750_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_nextMacroScope_1741_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_ngen_1742_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_auxDeclNGen_1743_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_traceState_1744_);
lean_ctor_set(v_reuseFailAlloc_1759_, 5, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1759_, 6, v_recordedDeps_1745_);
lean_ctor_set(v_reuseFailAlloc_1759_, 7, v_messages_1746_);
lean_ctor_set(v_reuseFailAlloc_1759_, 8, v_infoState_1747_);
lean_ctor_set(v_reuseFailAlloc_1759_, 9, v_snapshotTasks_1748_);
v___x_1756_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_st_ref_put(v___y_1735_, v___x_1756_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1752_);
return v___x_1758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1765_, lean_object* v_declName_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1765_, v_declName_1766_, v_a_1767_, v_a_1768_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1771_, lean_object* v_k_1772_, lean_object* v_t_1773_, lean_object* v_h_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1772_, v_t_1773_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1776_, lean_object* v_k_1777_, lean_object* v_t_1778_, lean_object* v_h_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1776_, v_k_1777_, v_t_1778_, v_h_1779_);
lean_dec(v_k_1777_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1781_, lean_object* v_s_1782_){
_start:
{
lean_object* v_casesTypes_1783_; lean_object* v_extThms_1784_; lean_object* v_funCC_1785_; lean_object* v_inj_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_casesTypes_1783_ = lean_ctor_get(v_s_1782_, 0);
v_extThms_1784_ = lean_ctor_get(v_s_1782_, 1);
v_funCC_1785_ = lean_ctor_get(v_s_1782_, 2);
v_inj_1786_ = lean_ctor_get(v_s_1782_, 4);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_s_1782_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v_s_1782_, 3);
lean_dec(v_unused_1794_);
v___x_1788_ = v_s_1782_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_inj_1786_);
lean_inc(v_funCC_1785_);
lean_inc(v_extThms_1784_);
lean_inc(v_casesTypes_1783_);
lean_dec(v_s_1782_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 3, v_a_1781_);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_casesTypes_1783_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_extThms_1784_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_funCC_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_a_1781_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_inj_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_1796_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
lean_ctor_set(v___x_1796_, 2, v___x_1795_);
lean_ctor_set(v___x_1796_, 3, v___x_1795_);
lean_ctor_set(v___x_1796_, 4, v___x_1795_);
lean_ctor_set(v___x_1796_, 5, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1797_, lean_object* v_declName_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v_ext_1806_; lean_object* v_toEnvExtension_1807_; lean_object* v_env_1808_; lean_object* v_asyncMode_1809_; lean_object* v___x_1810_; lean_object* v_ematch_1811_; lean_object* v___x_1812_; 
v___x_1804_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1805_ = lean_st_ref_get(v_a_1802_);
v_ext_1806_ = lean_ctor_get(v_ext_1797_, 1);
v_toEnvExtension_1807_ = lean_ctor_get(v_ext_1806_, 0);
v_env_1808_ = lean_ctor_get(v___x_1805_, 0);
lean_inc_ref(v_env_1808_);
lean_dec(v___x_1805_);
v_asyncMode_1809_ = lean_ctor_get(v_toEnvExtension_1807_, 2);
v___x_1810_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1804_, v_ext_1797_, v_env_1808_, v_asyncMode_1809_);
v_ematch_1811_ = lean_ctor_get(v___x_1810_, 3);
lean_inc_ref(v_ematch_1811_);
lean_dec(v___x_1810_);
v___x_1812_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1811_, v_declName_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1858_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1858_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1858_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___f_1817_; lean_object* v___x_1818_; lean_object* v_env_1819_; lean_object* v_nextMacroScope_1820_; lean_object* v_ngen_1821_; lean_object* v_auxDeclNGen_1822_; lean_object* v_traceState_1823_; lean_object* v_recordedDeps_1824_; lean_object* v_messages_1825_; lean_object* v_infoState_1826_; lean_object* v_snapshotTasks_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1856_; 
v___f_1817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1817_, 0, v_a_1813_);
v___x_1818_ = lean_st_ref_take(v_a_1802_);
v_env_1819_ = lean_ctor_get(v___x_1818_, 0);
v_nextMacroScope_1820_ = lean_ctor_get(v___x_1818_, 1);
v_ngen_1821_ = lean_ctor_get(v___x_1818_, 2);
v_auxDeclNGen_1822_ = lean_ctor_get(v___x_1818_, 3);
v_traceState_1823_ = lean_ctor_get(v___x_1818_, 4);
v_recordedDeps_1824_ = lean_ctor_get(v___x_1818_, 6);
v_messages_1825_ = lean_ctor_get(v___x_1818_, 7);
v_infoState_1826_ = lean_ctor_get(v___x_1818_, 8);
v_snapshotTasks_1827_ = lean_ctor_get(v___x_1818_, 9);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v___x_1818_, 5);
lean_dec(v_unused_1857_);
v___x_1829_ = v___x_1818_;
v_isShared_1830_ = v_isSharedCheck_1856_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snapshotTasks_1827_);
lean_inc(v_infoState_1826_);
lean_inc(v_messages_1825_);
lean_inc(v_recordedDeps_1824_);
lean_inc(v_traceState_1823_);
lean_inc(v_auxDeclNGen_1822_);
lean_inc(v_ngen_1821_);
lean_inc(v_nextMacroScope_1820_);
lean_inc(v_env_1819_);
lean_dec(v___x_1818_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1856_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1831_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1797_, v_env_1819_, v___f_1817_);
v___x_1832_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 5, v___x_1832_);
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1834_ = v___x_1829_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_nextMacroScope_1820_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_ngen_1821_);
lean_ctor_set(v_reuseFailAlloc_1855_, 3, v_auxDeclNGen_1822_);
lean_ctor_set(v_reuseFailAlloc_1855_, 4, v_traceState_1823_);
lean_ctor_set(v_reuseFailAlloc_1855_, 5, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1855_, 6, v_recordedDeps_1824_);
lean_ctor_set(v_reuseFailAlloc_1855_, 7, v_messages_1825_);
lean_ctor_set(v_reuseFailAlloc_1855_, 8, v_infoState_1826_);
lean_ctor_set(v_reuseFailAlloc_1855_, 9, v_snapshotTasks_1827_);
v___x_1834_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_mctx_1837_; lean_object* v_zetaDeltaFVarIds_1838_; lean_object* v_postponed_1839_; lean_object* v_diag_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1853_; 
v___x_1835_ = lean_st_ref_put(v_a_1802_, v___x_1834_);
v___x_1836_ = lean_st_ref_take(v_a_1800_);
v_mctx_1837_ = lean_ctor_get(v___x_1836_, 0);
v_zetaDeltaFVarIds_1838_ = lean_ctor_get(v___x_1836_, 2);
v_postponed_1839_ = lean_ctor_get(v___x_1836_, 3);
v_diag_1840_ = lean_ctor_get(v___x_1836_, 4);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v___x_1836_, 1);
lean_dec(v_unused_1854_);
v___x_1842_ = v___x_1836_;
v_isShared_1843_ = v_isSharedCheck_1853_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_diag_1840_);
lean_inc(v_postponed_1839_);
lean_inc(v_zetaDeltaFVarIds_1838_);
lean_inc(v_mctx_1837_);
lean_dec(v___x_1836_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1853_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 1, v___x_1845_);
v___x_1847_ = v___x_1842_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_mctx_1837_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_zetaDeltaFVarIds_1838_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v_postponed_1839_);
lean_ctor_set(v_reuseFailAlloc_1852_, 4, v_diag_1840_);
v___x_1847_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_st_ref_put(v_a_1800_, v___x_1847_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1844_);
v___x_1850_ = v___x_1815_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1844_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v_ext_1797_);
v_a_1859_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1812_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1812_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1867_, lean_object* v_declName_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1867_, v_declName_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1875_, lean_object* v_s_1876_){
_start:
{
lean_object* v_casesTypes_1877_; lean_object* v_extThms_1878_; lean_object* v_funCC_1879_; lean_object* v_ematch_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_casesTypes_1877_ = lean_ctor_get(v_s_1876_, 0);
v_extThms_1878_ = lean_ctor_get(v_s_1876_, 1);
v_funCC_1879_ = lean_ctor_get(v_s_1876_, 2);
v_ematch_1880_ = lean_ctor_get(v_s_1876_, 3);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_s_1876_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_s_1876_, 4);
lean_dec(v_unused_1888_);
v___x_1882_ = v_s_1876_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_ematch_1880_);
lean_inc(v_funCC_1879_);
lean_inc(v_extThms_1878_);
lean_inc(v_casesTypes_1877_);
lean_dec(v_s_1876_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 4, v_a_1875_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_casesTypes_1877_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_extThms_1878_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_funCC_1879_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_ematch_1880_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_a_1875_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1889_, lean_object* v_declName_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_ext_1898_; lean_object* v_toEnvExtension_1899_; lean_object* v_env_1900_; lean_object* v_asyncMode_1901_; lean_object* v___x_1902_; lean_object* v_inj_1903_; lean_object* v___x_1904_; 
v___x_1896_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1897_ = lean_st_ref_get(v_a_1894_);
v_ext_1898_ = lean_ctor_get(v_ext_1889_, 1);
v_toEnvExtension_1899_ = lean_ctor_get(v_ext_1898_, 0);
v_env_1900_ = lean_ctor_get(v___x_1897_, 0);
lean_inc_ref(v_env_1900_);
lean_dec(v___x_1897_);
v_asyncMode_1901_ = lean_ctor_get(v_toEnvExtension_1899_, 2);
v___x_1902_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1896_, v_ext_1889_, v_env_1900_, v_asyncMode_1901_);
v_inj_1903_ = lean_ctor_get(v___x_1902_, 4);
lean_inc_ref(v_inj_1903_);
lean_dec(v___x_1902_);
v___x_1904_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1903_, v_declName_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1950_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1950_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1950_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___f_1909_; lean_object* v___x_1910_; lean_object* v_env_1911_; lean_object* v_nextMacroScope_1912_; lean_object* v_ngen_1913_; lean_object* v_auxDeclNGen_1914_; lean_object* v_traceState_1915_; lean_object* v_recordedDeps_1916_; lean_object* v_messages_1917_; lean_object* v_infoState_1918_; lean_object* v_snapshotTasks_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1948_; 
v___f_1909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1909_, 0, v_a_1905_);
v___x_1910_ = lean_st_ref_take(v_a_1894_);
v_env_1911_ = lean_ctor_get(v___x_1910_, 0);
v_nextMacroScope_1912_ = lean_ctor_get(v___x_1910_, 1);
v_ngen_1913_ = lean_ctor_get(v___x_1910_, 2);
v_auxDeclNGen_1914_ = lean_ctor_get(v___x_1910_, 3);
v_traceState_1915_ = lean_ctor_get(v___x_1910_, 4);
v_recordedDeps_1916_ = lean_ctor_get(v___x_1910_, 6);
v_messages_1917_ = lean_ctor_get(v___x_1910_, 7);
v_infoState_1918_ = lean_ctor_get(v___x_1910_, 8);
v_snapshotTasks_1919_ = lean_ctor_get(v___x_1910_, 9);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; 
v_unused_1949_ = lean_ctor_get(v___x_1910_, 5);
lean_dec(v_unused_1949_);
v___x_1921_ = v___x_1910_;
v_isShared_1922_ = v_isSharedCheck_1948_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_snapshotTasks_1919_);
lean_inc(v_infoState_1918_);
lean_inc(v_messages_1917_);
lean_inc(v_recordedDeps_1916_);
lean_inc(v_traceState_1915_);
lean_inc(v_auxDeclNGen_1914_);
lean_inc(v_ngen_1913_);
lean_inc(v_nextMacroScope_1912_);
lean_inc(v_env_1911_);
lean_dec(v___x_1910_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1948_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1889_, v_env_1911_, v___f_1909_);
v___x_1924_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 5, v___x_1924_);
lean_ctor_set(v___x_1921_, 0, v___x_1923_);
v___x_1926_ = v___x_1921_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_nextMacroScope_1912_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_ngen_1913_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_auxDeclNGen_1914_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_traceState_1915_);
lean_ctor_set(v_reuseFailAlloc_1947_, 5, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1947_, 6, v_recordedDeps_1916_);
lean_ctor_set(v_reuseFailAlloc_1947_, 7, v_messages_1917_);
lean_ctor_set(v_reuseFailAlloc_1947_, 8, v_infoState_1918_);
lean_ctor_set(v_reuseFailAlloc_1947_, 9, v_snapshotTasks_1919_);
v___x_1926_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_mctx_1929_; lean_object* v_zetaDeltaFVarIds_1930_; lean_object* v_postponed_1931_; lean_object* v_diag_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1945_; 
v___x_1927_ = lean_st_ref_put(v_a_1894_, v___x_1926_);
v___x_1928_ = lean_st_ref_take(v_a_1892_);
v_mctx_1929_ = lean_ctor_get(v___x_1928_, 0);
v_zetaDeltaFVarIds_1930_ = lean_ctor_get(v___x_1928_, 2);
v_postponed_1931_ = lean_ctor_get(v___x_1928_, 3);
v_diag_1932_ = lean_ctor_get(v___x_1928_, 4);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1928_, 1);
lean_dec(v_unused_1946_);
v___x_1934_ = v___x_1928_;
v_isShared_1935_ = v_isSharedCheck_1945_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_diag_1932_);
lean_inc(v_postponed_1931_);
lean_inc(v_zetaDeltaFVarIds_1930_);
lean_inc(v_mctx_1929_);
lean_dec(v___x_1928_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1945_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v___x_1937_);
v___x_1939_ = v___x_1934_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_mctx_1929_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_zetaDeltaFVarIds_1930_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_postponed_1931_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_diag_1932_);
v___x_1939_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_st_ref_put(v_a_1892_, v___x_1939_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1936_);
v___x_1942_ = v___x_1907_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1936_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_ext_1889_);
v_a_1951_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1904_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1904_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1959_, lean_object* v_declName_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1959_, v_declName_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
return v_res_1966_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1967_, lean_object* v_i_1968_, lean_object* v_k_1969_){
_start:
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = lean_array_get_size(v_keys_1967_);
v___x_1971_ = lean_nat_dec_lt(v_i_1968_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_dec(v_i_1968_);
return v___x_1971_;
}
else
{
lean_object* v_k_x27_1972_; uint8_t v___x_1973_; 
v_k_x27_1972_ = lean_array_fget_borrowed(v_keys_1967_, v_i_1968_);
v___x_1973_ = lean_name_eq(v_k_1969_, v_k_x27_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_add(v_i_1968_, v___x_1974_);
lean_dec(v_i_1968_);
v_i_1968_ = v___x_1975_;
goto _start;
}
else
{
lean_dec(v_i_1968_);
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1977_, lean_object* v_i_1978_, lean_object* v_k_1979_){
_start:
{
uint8_t v_res_1980_; lean_object* v_r_1981_; 
v_res_1980_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1977_, v_i_1978_, v_k_1979_);
lean_dec(v_k_1979_);
lean_dec_ref(v_keys_1977_);
v_r_1981_ = lean_box(v_res_1980_);
return v_r_1981_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1982_, size_t v_x_1983_, lean_object* v_x_1984_){
_start:
{
if (lean_obj_tag(v_x_1982_) == 0)
{
lean_object* v_es_1985_; lean_object* v___x_1986_; size_t v___x_1987_; size_t v___x_1988_; lean_object* v_j_1989_; lean_object* v___x_1990_; 
v_es_1985_ = lean_ctor_get(v_x_1982_, 0);
v___x_1986_ = lean_box(2);
v___x_1987_ = ((size_t)31ULL);
v___x_1988_ = lean_usize_land(v_x_1983_, v___x_1987_);
v_j_1989_ = lean_usize_to_nat(v___x_1988_);
v___x_1990_ = lean_array_get_borrowed(v___x_1986_, v_es_1985_, v_j_1989_);
lean_dec(v_j_1989_);
switch(lean_obj_tag(v___x_1990_))
{
case 0:
{
lean_object* v_key_1991_; uint8_t v___x_1992_; 
v_key_1991_ = lean_ctor_get(v___x_1990_, 0);
v___x_1992_ = lean_name_eq(v_x_1984_, v_key_1991_);
return v___x_1992_;
}
case 1:
{
lean_object* v_node_1993_; size_t v___x_1994_; size_t v___x_1995_; 
v_node_1993_ = lean_ctor_get(v___x_1990_, 0);
v___x_1994_ = ((size_t)5ULL);
v___x_1995_ = lean_usize_shift_right(v_x_1983_, v___x_1994_);
v_x_1982_ = v_node_1993_;
v_x_1983_ = v___x_1995_;
goto _start;
}
default: 
{
uint8_t v___x_1997_; 
v___x_1997_ = 0;
return v___x_1997_;
}
}
}
else
{
lean_object* v_ks_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_ks_1998_ = lean_ctor_get(v_x_1982_, 0);
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1998_, v___x_1999_, v_x_1984_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
size_t v_x_328__boxed_2004_; uint8_t v_res_2005_; lean_object* v_r_2006_; 
v_x_328__boxed_2004_ = lean_unbox_usize(v_x_2002_);
lean_dec(v_x_2002_);
v_res_2005_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2001_, v_x_328__boxed_2004_, v_x_2003_);
lean_dec(v_x_2003_);
lean_dec_ref(v_x_2001_);
v_r_2006_ = lean_box(v_res_2005_);
return v_r_2006_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
uint64_t v___y_2010_; 
if (lean_obj_tag(v_x_2008_) == 0)
{
uint64_t v___x_2013_; 
v___x_2013_ = 1723ULL;
v___y_2010_ = v___x_2013_;
goto v___jp_2009_;
}
else
{
uint64_t v_hash_2014_; 
v_hash_2014_ = lean_ctor_get_uint64(v_x_2008_, sizeof(void*)*2);
v___y_2010_ = v_hash_2014_;
goto v___jp_2009_;
}
v___jp_2009_:
{
size_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_uint64_to_usize(v___y_2010_);
v___x_2012_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2007_, v___x_2011_, v_x_2008_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
uint8_t v_res_2017_; lean_object* v_r_2018_; 
v_res_2017_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2015_, v_x_2016_);
lean_dec(v_x_2016_);
lean_dec_ref(v_x_2015_);
v_r_2018_ = lean_box(v_res_2017_);
return v_r_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2019_, lean_object* v_declName_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v_ext_2025_; lean_object* v_toEnvExtension_2026_; lean_object* v_env_2027_; lean_object* v_asyncMode_2028_; lean_object* v___x_2029_; lean_object* v_extThms_2030_; uint8_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2023_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2024_ = lean_st_ref_get(v_a_2021_);
v_ext_2025_ = lean_ctor_get(v_ext_2019_, 1);
v_toEnvExtension_2026_ = lean_ctor_get(v_ext_2025_, 0);
v_env_2027_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_ref(v_env_2027_);
lean_dec(v___x_2024_);
v_asyncMode_2028_ = lean_ctor_get(v_toEnvExtension_2026_, 2);
v___x_2029_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2023_, v_ext_2019_, v_env_2027_, v_asyncMode_2028_);
v_extThms_2030_ = lean_ctor_get(v___x_2029_, 1);
lean_inc_ref(v_extThms_2030_);
lean_dec(v___x_2029_);
v___x_2031_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2030_, v_declName_2020_);
lean_dec_ref(v_extThms_2030_);
v___x_2032_ = lean_box(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2034_, lean_object* v_declName_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2034_, v_declName_2035_, v_a_2036_);
lean_dec(v_a_2036_);
lean_dec(v_declName_2035_);
lean_dec_ref(v_ext_2034_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2039_, lean_object* v_declName_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2039_, v_declName_2040_, v_a_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2045_, lean_object* v_declName_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2045_, v_declName_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_declName_2046_);
lean_dec_ref(v_ext_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2052_, v_x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2055_, v_x_2056_, v_x_2057_);
lean_dec(v_x_2057_);
lean_dec_ref(v_x_2056_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2060_, lean_object* v_x_2061_, size_t v_x_2062_, lean_object* v_x_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2061_, v_x_2062_, v_x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
size_t v_x_413__boxed_2069_; uint8_t v_res_2070_; lean_object* v_r_2071_; 
v_x_413__boxed_2069_ = lean_unbox_usize(v_x_2067_);
lean_dec(v_x_2067_);
v_res_2070_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2065_, v_x_2066_, v_x_413__boxed_2069_, v_x_2068_);
lean_dec(v_x_2068_);
lean_dec_ref(v_x_2066_);
v_r_2071_ = lean_box(v_res_2070_);
return v_r_2071_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2072_, lean_object* v_keys_2073_, lean_object* v_vals_2074_, lean_object* v_heq_2075_, lean_object* v_i_2076_, lean_object* v_k_2077_){
_start:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2073_, v_i_2076_, v_k_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2079_, lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_heq_2082_, lean_object* v_i_2083_, lean_object* v_k_2084_){
_start:
{
uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_res_2085_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2079_, v_keys_2080_, v_vals_2081_, v_heq_2082_, v_i_2083_, v_k_2084_);
lean_dec(v_k_2084_);
lean_dec_ref(v_vals_2081_);
lean_dec_ref(v_keys_2080_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2087_, lean_object* v_declName_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_ext_2093_; lean_object* v_toEnvExtension_2094_; lean_object* v_env_2095_; lean_object* v_asyncMode_2096_; lean_object* v___x_2097_; lean_object* v_inj_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2091_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2092_ = lean_st_ref_get(v_a_2089_);
v_ext_2093_ = lean_ctor_get(v_ext_2087_, 1);
v_toEnvExtension_2094_ = lean_ctor_get(v_ext_2093_, 0);
v_env_2095_ = lean_ctor_get(v___x_2092_, 0);
lean_inc_ref(v_env_2095_);
lean_dec(v___x_2092_);
v_asyncMode_2096_ = lean_ctor_get(v_toEnvExtension_2094_, 2);
v___x_2097_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2091_, v_ext_2087_, v_env_2095_, v_asyncMode_2096_);
v_inj_2098_ = lean_ctor_get(v___x_2097_, 4);
lean_inc_ref(v_inj_2098_);
lean_dec(v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_declName_2088_);
v___x_2100_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2098_, v___x_2099_);
lean_dec_ref_known(v___x_2099_, 1);
lean_dec_ref(v_inj_2098_);
v___x_2101_ = lean_box(v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2103_, lean_object* v_declName_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2103_, v_declName_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_ext_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2108_, lean_object* v_declName_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2108_, v_declName_2109_, v_a_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2114_, lean_object* v_declName_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2114_, v_declName_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_ext_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2120_, lean_object* v_declName_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_ext_2126_; lean_object* v_toEnvExtension_2127_; lean_object* v_env_2128_; lean_object* v_asyncMode_2129_; lean_object* v___x_2130_; lean_object* v_funCC_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2124_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2125_ = lean_st_ref_get(v_a_2122_);
v_ext_2126_ = lean_ctor_get(v_ext_2120_, 1);
v_toEnvExtension_2127_ = lean_ctor_get(v_ext_2126_, 0);
v_env_2128_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_ref(v_env_2128_);
lean_dec(v___x_2125_);
v_asyncMode_2129_ = lean_ctor_get(v_toEnvExtension_2127_, 2);
v___x_2130_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2124_, v_ext_2120_, v_env_2128_, v_asyncMode_2129_);
v_funCC_2131_ = lean_ctor_get(v___x_2130_, 2);
lean_inc(v_funCC_2131_);
lean_dec(v___x_2130_);
v___x_2132_ = l_Lean_NameSet_contains(v_funCC_2131_, v_declName_2121_);
lean_dec(v_funCC_2131_);
v___x_2133_ = lean_box(v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2135_, lean_object* v_declName_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2135_, v_declName_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec(v_declName_2136_);
lean_dec_ref(v_ext_2135_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2140_, lean_object* v_declName_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2140_, v_declName_2141_, v_a_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2146_, lean_object* v_declName_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2146_, v_declName_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_declName_2147_);
lean_dec_ref(v_ext_2146_);
return v_res_2151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2176_ = l_Lean_mkAtom(v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2179_ = lean_array_push(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2189_ = l_Lean_mkAtom(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2195_ = lean_box(2);
v___x_2196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
lean_ctor_set(v___x_2196_, 2, v___x_2193_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2199_ = lean_array_push(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2202_ = lean_box(2);
v___x_2203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2201_);
lean_ctor_set(v___x_2203_, 2, v___x_2200_);
return v___x_2203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2206_ = lean_array_push(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2209_ = lean_box(2);
v___x_2210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2208_);
lean_ctor_set(v___x_2210_, 2, v___x_2207_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2213_ = lean_array_push(v___x_2212_, v___x_2211_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2216_ = lean_box(2);
v___x_2217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
lean_ctor_set(v___x_2217_, 2, v___x_2214_);
return v___x_2217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2220_ = lean_array_push(v___x_2219_, v___x_2218_);
return v___x_2220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2223_ = lean_box(2);
v___x_2224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v___x_2222_);
lean_ctor_set(v___x_2224_, 2, v___x_2221_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2226_, lean_object* v_ext_2227_, lean_object* v_____r_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = 0;
lean_inc(v_declName_2226_);
v___x_2235_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2226_, v___x_2234_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; uint8_t v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = lean_unbox(v_a_2236_);
lean_dec(v_a_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v_a_2239_; uint8_t v___x_2240_; 
v___x_2238_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2227_, v_declName_2226_, v___y_2232_);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = lean_unbox(v_a_2239_);
lean_dec(v_a_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v_a_2242_; uint8_t v___x_2243_; 
lean_inc(v_declName_2226_);
v___x_2241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2227_, v_declName_2226_, v___y_2232_);
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref(v___x_2241_);
v___x_2243_ = lean_unbox(v_a_2242_);
lean_dec(v_a_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v_a_2245_; uint8_t v___x_2246_; 
v___x_2244_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2227_, v_declName_2226_, v___y_2232_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = lean_unbox(v_a_2245_);
lean_dec(v_a_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2227_, v_declName_2226_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2227_, v_declName_2226_, v___y_2231_, v___y_2232_);
return v___x_2248_;
}
}
else
{
lean_object* v___x_2249_; 
v___x_2249_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2227_, v_declName_2226_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
return v___x_2249_;
}
}
else
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2227_, v_declName_2226_, v___y_2231_, v___y_2232_);
return v___x_2250_;
}
}
else
{
lean_object* v___x_2251_; 
v___x_2251_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2227_, v_declName_2226_, v___y_2231_, v___y_2232_);
return v___x_2251_;
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref(v_ext_2227_);
lean_dec(v_declName_2226_);
v_a_2252_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2235_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2235_);
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
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2260_, lean_object* v_ext_2261_, lean_object* v_____r_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2260_, v_ext_2261_, v_____r_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; lean_object* v_env_2276_; lean_object* v___x_2277_; lean_object* v_toCold_2278_; lean_object* v_mctx_2279_; lean_object* v_lctx_2280_; lean_object* v_options_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2275_ = lean_st_ref_get(v___y_2273_);
v_env_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc_ref(v_env_2276_);
lean_dec(v___x_2275_);
v___x_2277_ = lean_st_ref_get(v___y_2271_);
v_toCold_2278_ = lean_ctor_get(v___y_2272_, 0);
v_mctx_2279_ = lean_ctor_get(v___x_2277_, 0);
lean_inc_ref(v_mctx_2279_);
lean_dec(v___x_2277_);
v_lctx_2280_ = lean_ctor_get(v___y_2270_, 2);
v_options_2281_ = lean_ctor_get(v_toCold_2278_, 2);
lean_inc_ref(v_options_2281_);
lean_inc_ref(v_lctx_2280_);
v___x_2282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2282_, 0, v_env_2276_);
lean_ctor_set(v___x_2282_, 1, v_mctx_2279_);
lean_ctor_set(v___x_2282_, 2, v_lctx_2280_);
lean_ctor_set(v___x_2282_, 3, v_options_2281_);
v___x_2283_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v_msgData_2269_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_ref_2298_; lean_object* v___x_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_ref_2298_ = lean_ctor_get(v___y_2295_, 2);
v___x_2299_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
lean_inc(v_ref_2298_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_ref_2298_);
lean_ctor_set(v___x_2304_, 1, v_a_2300_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set_tag(v___x_2302_, 1);
lean_ctor_set(v___x_2302_, 0, v___x_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2315_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2322_; uint64_t v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2323_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2326_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set_uint64(v___x_2326_, sizeof(void*)*1, v___x_2324_);
return v___x_2326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_box(1);
v___x_2330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2330_);
lean_ctor_set(v___x_2332_, 2, v___x_2329_);
return v___x_2332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2336_ = lean_unsigned_to_nat(0u);
v___x_2337_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
lean_ctor_set(v___x_2337_, 2, v___x_2336_);
lean_ctor_set(v___x_2337_, 3, v___x_2336_);
lean_ctor_set(v___x_2337_, 4, v___x_2335_);
lean_ctor_set(v___x_2337_, 5, v___x_2335_);
lean_ctor_set(v___x_2337_, 6, v___x_2335_);
lean_ctor_set(v___x_2337_, 7, v___x_2335_);
lean_ctor_set(v___x_2337_, 8, v___x_2335_);
lean_ctor_set(v___x_2337_, 9, v___x_2335_);
lean_ctor_set(v___x_2337_, 10, v___x_2335_);
return v___x_2337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2339_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
lean_ctor_set(v___x_2339_, 2, v___x_2338_);
lean_ctor_set(v___x_2339_, 3, v___x_2338_);
lean_ctor_set(v___x_2339_, 4, v___x_2338_);
lean_ctor_set(v___x_2339_, 5, v___x_2338_);
return v___x_2339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
lean_ctor_set(v___x_2341_, 2, v___x_2340_);
lean_ctor_set(v___x_2341_, 3, v___x_2340_);
lean_ctor_set(v___x_2341_, 4, v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_2350_ = l_Lean_stringToMessageData(v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_2351_, lean_object* v___x_2352_, uint8_t v_showInfo_2353_, lean_object* v_attrName_2354_, lean_object* v_declName_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v___x_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___y_2374_; 
v___x_2359_ = 1;
v___x_2360_ = 0;
v___x_2361_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_2366_ = lean_box(0);
lean_inc(v___x_2352_);
v___x_2367_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2367_, 0, v___x_2361_);
lean_ctor_set(v___x_2367_, 1, v___x_2352_);
lean_ctor_set(v___x_2367_, 2, v___x_2364_);
lean_ctor_set(v___x_2367_, 3, v___x_2365_);
lean_ctor_set(v___x_2367_, 4, v___x_2366_);
lean_ctor_set(v___x_2367_, 5, v___x_2362_);
lean_ctor_set(v___x_2367_, 6, v___x_2366_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*7, v___x_2360_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*7 + 1, v___x_2360_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*7 + 2, v___x_2360_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*7 + 3, v___x_2359_);
v___x_2368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_2369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2368_);
lean_ctor_set(v___x_2371_, 1, v___x_2369_);
lean_ctor_set(v___x_2371_, 2, v___x_2352_);
lean_ctor_set(v___x_2371_, 3, v___x_2363_);
lean_ctor_set(v___x_2371_, 4, v___x_2370_);
v___x_2372_ = lean_st_mk_ref(v___x_2371_);
if (v_showInfo_2353_ == 0)
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec(v_attrName_2354_);
v___x_2384_ = lean_box(0);
v___x_2385_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2355_, v_ext_2351_, v___x_2384_, v___x_2367_, v___x_2372_, v___y_2356_, v___y_2357_);
lean_dec_ref_known(v___x_2367_, 7);
v___y_2374_ = v___x_2385_;
goto v___jp_2373_;
}
else
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v_declName_2355_);
lean_dec_ref(v_ext_2351_);
v___x_2386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_2387_ = l_Lean_MessageData_ofName(v_attrName_2354_);
lean_inc_ref(v___x_2387_);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2387_);
v___x_2392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2393_, v___x_2367_, v___x_2372_, v___y_2356_, v___y_2357_);
lean_dec_ref_known(v___x_2367_, 7);
v___y_2374_ = v___x_2394_;
goto v___jp_2373_;
}
v___jp_2373_:
{
if (lean_obj_tag(v___y_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2383_; 
v_a_2375_ = lean_ctor_get(v___y_2374_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___y_2374_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2377_ = v___y_2374_;
v_isShared_2378_ = v_isSharedCheck_2383_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___y_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2383_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2379_ = lean_st_ref_get(v___x_2372_);
lean_dec(v___x_2372_);
lean_dec(v___x_2379_);
if (v_isShared_2378_ == 0)
{
v___x_2381_ = v___x_2377_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2375_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
else
{
lean_dec(v___x_2372_);
return v___y_2374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_2395_, lean_object* v___x_2396_, lean_object* v_showInfo_2397_, lean_object* v_attrName_2398_, lean_object* v_declName_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
uint8_t v_showInfo_boxed_2403_; lean_object* v_res_2404_; 
v_showInfo_boxed_2403_ = lean_unbox(v_showInfo_2397_);
v_res_2404_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_2395_, v___x_2396_, v_showInfo_boxed_2403_, v_attrName_2398_, v_declName_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2407_, uint8_t v_attrKind_2408_, uint8_t v_showInfo_2409_, uint8_t v_minIndexable_2410_, lean_object* v_as_x27_2411_, lean_object* v_b_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
if (lean_obj_tag(v_as_x27_2411_) == 0)
{
lean_object* v___x_2418_; 
lean_dec_ref(v_ext_2407_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_b_2412_);
return v___x_2418_;
}
else
{
lean_object* v_head_2419_; lean_object* v_tail_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_head_2419_ = lean_ctor_get(v_as_x27_2411_, 0);
v_tail_2420_ = lean_ctor_get(v_as_x27_2411_, 1);
v___x_2421_ = lean_box(0);
v___x_2422_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2416_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2419_);
lean_inc_ref(v_ext_2407_);
v___x_2425_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2407_, v_head_2419_, v_attrKind_2408_, v___x_2424_, v_a_2423_, v_showInfo_2409_, v_minIndexable_2410_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_dec_ref_known(v___x_2425_, 1);
v_as_x27_2411_ = v_tail_2420_;
v_b_2412_ = v___x_2421_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2407_);
return v___x_2425_;
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec_ref(v_ext_2407_);
v_a_2427_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2422_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2422_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2435_, lean_object* v_attrKind_2436_, lean_object* v_showInfo_2437_, lean_object* v_minIndexable_2438_, lean_object* v_as_x27_2439_, lean_object* v_b_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
uint8_t v_attrKind_boxed_2446_; uint8_t v_showInfo_boxed_2447_; uint8_t v_minIndexable_boxed_2448_; lean_object* v_res_2449_; 
v_attrKind_boxed_2446_ = lean_unbox(v_attrKind_2436_);
v_showInfo_boxed_2447_ = lean_unbox(v_showInfo_2437_);
v_minIndexable_boxed_2448_ = lean_unbox(v_minIndexable_2438_);
v_res_2449_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2435_, v_attrKind_boxed_2446_, v_showInfo_boxed_2447_, v_minIndexable_boxed_2448_, v_as_x27_2439_, v_b_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v_as_x27_2439_);
return v_res_2449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2461_ = l_Lean_stringToMessageData(v___x_2460_);
return v___x_2461_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2467_ = l_Lean_stringToMessageData(v___x_2466_);
return v___x_2467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2470_ = l_Lean_stringToMessageData(v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2473_ = l_Lean_stringToMessageData(v___x_2472_);
return v___x_2473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16));
v___x_2476_ = l_Lean_stringToMessageData(v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18));
v___x_2479_ = l_Lean_stringToMessageData(v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_2480_, uint8_t v___x_2481_, uint8_t v_attrKind_2482_, lean_object* v_stx_2483_, lean_object* v_ext_2484_, uint8_t v_showInfo_2485_, uint8_t v_minIndexable_2486_, lean_object* v_attrName_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2483_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
switch(lean_obj_tag(v_a_2518_))
{
case 0:
{
lean_object* v_k_2519_; 
lean_dec(v_attrName_2487_);
lean_dec(v_stx_2483_);
v_k_2519_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_k_2519_);
lean_dec_ref_known(v_a_2518_, 1);
if (lean_obj_tag(v_k_2519_) == 9)
{
lean_object* v___x_2520_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_declName_2480_);
v___x_2520_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2490_, v___y_2491_);
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2491_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
v___x_2523_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2484_, v_declName_2480_, v_attrKind_2482_, v_k_2519_, v_a_2522_, v_showInfo_2485_, v_minIndexable_2486_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2523_;
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_k_2519_);
lean_dec_ref(v_ext_2484_);
lean_dec(v_declName_2480_);
v_a_2524_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2521_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2521_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2532_; lean_object* v___x_2533_; 
lean_dec(v_attrName_2487_);
lean_dec(v_stx_2483_);
v_eager_2532_ = lean_ctor_get_uint8(v_a_2518_, 0);
lean_dec_ref_known(v_a_2518_, 0);
v___x_2533_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2484_, v_declName_2480_, v_eager_2532_, v_attrKind_2482_, v___y_2490_, v___y_2491_);
return v___x_2533_;
}
case 2:
{
lean_object* v___x_2534_; 
lean_dec(v_stx_2483_);
lean_inc(v_declName_2480_);
v___x_2534_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2480_, v___x_2481_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
if (lean_obj_tag(v_a_2535_) == 1)
{
lean_object* v_val_2536_; lean_object* v_ctors_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v_attrName_2487_);
lean_dec(v_declName_2480_);
v_val_2536_ = lean_ctor_get(v_a_2535_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v_a_2535_, 1);
v_ctors_2537_ = lean_ctor_get(v_val_2536_, 4);
lean_inc(v_ctors_2537_);
lean_dec(v_val_2536_);
v___x_2538_ = lean_box(0);
v___x_2539_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2484_, v_attrKind_2482_, v_showInfo_2485_, v_minIndexable_2486_, v_ctors_2537_, v___x_2538_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v_ctors_2537_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v___x_2539_, 0);
lean_dec(v_unused_2547_);
v___x_2541_ = v___x_2539_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_dec(v___x_2539_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2538_);
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2538_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
return v___x_2539_;
}
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_a_2535_);
lean_dec_ref(v_ext_2484_);
v___x_2548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2549_ = l_Lean_MessageData_ofName(v_attrName_2487_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = l_Lean_MessageData_ofConstName(v_declName_2480_, v___x_2481_);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2556_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2557_;
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_attrName_2487_);
lean_dec_ref(v_ext_2484_);
lean_dec(v_declName_2480_);
v_a_2558_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2534_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2534_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
case 3:
{
lean_object* v___x_2566_; 
lean_dec(v_attrName_2487_);
lean_inc(v_declName_2480_);
v___x_2566_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2480_, v___x_2481_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
if (lean_obj_tag(v_a_2567_) == 1)
{
lean_object* v_val_2568_; lean_object* v___x_2569_; 
lean_dec(v_stx_2483_);
lean_dec(v_declName_2480_);
v_val_2568_ = lean_ctor_get(v_a_2567_, 0);
lean_inc_n(v_val_2568_, 2);
lean_dec_ref_known(v_a_2567_, 1);
lean_inc_ref(v_ext_2484_);
v___x_2569_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2484_, v_val_2568_, v___x_2481_, v_attrKind_2482_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2570_; 
lean_dec_ref_known(v___x_2569_, 1);
v___x_2570_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2568_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2591_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2591_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2591_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
if (lean_obj_tag(v_a_2571_) == 1)
{
lean_object* v_val_2575_; lean_object* v_ctors_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_del_object(v___x_2573_);
v_val_2575_ = lean_ctor_get(v_a_2571_, 0);
lean_inc(v_val_2575_);
lean_dec_ref_known(v_a_2571_, 1);
v_ctors_2576_ = lean_ctor_get(v_val_2575_, 4);
lean_inc(v_ctors_2576_);
lean_dec(v_val_2575_);
v___x_2577_ = lean_box(0);
v___x_2578_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2484_, v_attrKind_2482_, v_showInfo_2485_, v_minIndexable_2486_, v_ctors_2576_, v___x_2577_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v_ctors_2576_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2578_, 0);
lean_dec(v_unused_2586_);
v___x_2580_ = v___x_2578_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_dec(v___x_2578_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2577_);
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2577_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
return v___x_2578_;
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_dec(v_a_2571_);
lean_dec_ref(v_ext_2484_);
v___x_2587_ = lean_box(0);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2587_);
v___x_2589_ = v___x_2573_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_ext_2484_);
v_a_2592_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2570_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2570_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_dec(v_val_2568_);
lean_dec_ref(v_ext_2484_);
return v___x_2569_;
}
}
else
{
lean_object* v___x_2600_; 
lean_dec(v_a_2567_);
v___x_2600_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2491_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2484_, v_stx_2483_, v_declName_2480_, v_attrKind_2482_, v_a_2601_, v_minIndexable_2486_, v_showInfo_2485_, v___x_2481_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2602_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
lean_dec(v_declName_2480_);
v_a_2603_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2600_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2600_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
lean_dec(v_declName_2480_);
v_a_2611_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2566_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2566_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
case 4:
{
lean_object* v___x_2619_; 
lean_dec(v_attrName_2487_);
lean_dec(v_stx_2483_);
v___x_2619_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2484_, v_declName_2480_, v_attrKind_2482_, v___y_2490_, v___y_2491_);
return v___x_2619_;
}
case 5:
{
lean_object* v_prio_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
v_prio_2620_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_prio_2620_);
lean_dec_ref_known(v_a_2518_, 1);
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2622_ = lean_name_eq(v_attrName_2487_, v___x_2621_);
lean_dec(v_attrName_2487_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec(v_prio_2620_);
lean_dec(v_declName_2480_);
v___x_2623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2624_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2623_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2624_;
}
else
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2480_, v_attrKind_2482_, v_prio_2620_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2625_;
}
}
case 6:
{
lean_object* v___x_2626_; 
lean_dec(v_attrName_2487_);
lean_dec(v_stx_2483_);
v___x_2626_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2484_, v_declName_2480_, v_attrKind_2482_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2626_;
}
case 7:
{
lean_object* v___x_2627_; 
lean_dec(v_attrName_2487_);
lean_dec(v_stx_2483_);
v___x_2627_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2484_, v_declName_2480_, v_attrKind_2482_, v___y_2490_, v___y_2491_);
return v___x_2627_;
}
case 8:
{
uint8_t v_post_2628_; uint8_t v_inv_2629_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
v_post_2628_ = lean_ctor_get_uint8(v_a_2518_, 0);
v_inv_2629_ = lean_ctor_get_uint8(v_a_2518_, 1);
lean_dec_ref_known(v_a_2518_, 0);
v___x_2638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2639_ = lean_name_eq(v_attrName_2487_, v___x_2638_);
lean_dec(v_attrName_2487_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec(v_declName_2480_);
v___x_2640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2641_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2640_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2641_;
}
else
{
v___y_2631_ = v___y_2488_;
v___y_2632_ = v___y_2489_;
v___y_2633_ = v___y_2490_;
v___y_2634_ = v___y_2491_;
goto v___jp_2630_;
}
v___jp_2630_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = l_Lean_Meta_Grind_normExt;
v___x_2636_ = lean_unsigned_to_nat(1000u);
v___x_2637_ = l_Lean_Meta_addSimpTheorem(v___x_2635_, v_declName_2480_, v_post_2628_, v_inv_2629_, v_attrKind_2482_, v___x_2636_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2637_;
}
}
case 9:
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2643_ = lean_name_eq(v_attrName_2487_, v___x_2642_);
lean_dec(v_attrName_2487_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec(v_declName_2480_);
v___x_2644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2645_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2644_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2645_;
}
else
{
goto v___jp_2493_;
}
}
case 10:
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
v___x_2646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2647_ = lean_name_eq(v_attrName_2487_, v___x_2646_);
lean_dec(v_attrName_2487_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v_declName_2480_);
v___x_2648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17);
v___x_2649_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2648_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_2480_, v_attrKind_2482_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2650_;
}
}
default: 
{
lean_object* v___x_2651_; uint8_t v___x_2652_; 
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2652_ = lean_name_eq(v_attrName_2487_, v___x_2651_);
lean_dec(v_attrName_2487_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v_declName_2480_);
v___x_2653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19);
v___x_2654_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2653_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2654_;
}
else
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_2480_, v_attrKind_2482_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_attrName_2487_);
lean_dec_ref(v_ext_2484_);
lean_dec(v_stx_2483_);
lean_dec(v_declName_2480_);
v_a_2656_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2517_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2517_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
v___jp_2493_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = l_Lean_Meta_Grind_normExt;
v___x_2495_ = lean_unsigned_to_nat(1000u);
v___x_2496_ = l_Lean_Meta_addDeclToUnfold(v___x_2494_, v_declName_2480_, v___x_2481_, v___x_2481_, v___x_2495_, v_attrKind_2482_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2508_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2508_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2508_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_unbox(v_a_2497_);
lean_dec(v_a_2497_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_del_object(v___x_2499_);
v___x_2502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2503_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2502_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_box(0);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2504_);
v___x_2506_ = v___x_2499_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
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
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2496_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2496_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_2664_, lean_object* v___x_2665_, lean_object* v_attrKind_2666_, lean_object* v_stx_2667_, lean_object* v_ext_2668_, lean_object* v_showInfo_2669_, lean_object* v_minIndexable_2670_, lean_object* v_attrName_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
uint8_t v___x_15179__boxed_2677_; uint8_t v_attrKind_boxed_2678_; uint8_t v_showInfo_boxed_2679_; uint8_t v_minIndexable_boxed_2680_; lean_object* v_res_2681_; 
v___x_15179__boxed_2677_ = lean_unbox(v___x_2665_);
v_attrKind_boxed_2678_ = lean_unbox(v_attrKind_2666_);
v_showInfo_boxed_2679_ = lean_unbox(v_showInfo_2669_);
v_minIndexable_boxed_2680_ = lean_unbox(v_minIndexable_2670_);
v_res_2681_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_2664_, v___x_15179__boxed_2677_, v_attrKind_boxed_2678_, v_stx_2667_, v_ext_2668_, v_showInfo_boxed_2679_, v_minIndexable_boxed_2680_, v_attrName_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
return v_res_2681_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2682_; double v___x_2683_; 
v___x_2682_ = lean_unsigned_to_nat(0u);
v___x_2683_ = lean_float_of_nat(v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2687_, lean_object* v_msg_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_ref_2694_; lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2741_; 
v_ref_2694_ = lean_ctor_get(v___y_2691_, 2);
v___x_2695_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2741_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2741_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v_traceState_2701_; lean_object* v_env_2702_; lean_object* v_nextMacroScope_2703_; lean_object* v_ngen_2704_; lean_object* v_auxDeclNGen_2705_; lean_object* v_cache_2706_; lean_object* v_recordedDeps_2707_; lean_object* v_messages_2708_; lean_object* v_infoState_2709_; lean_object* v_snapshotTasks_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2740_; 
v___x_2700_ = lean_st_ref_take(v___y_2692_);
v_traceState_2701_ = lean_ctor_get(v___x_2700_, 4);
v_env_2702_ = lean_ctor_get(v___x_2700_, 0);
v_nextMacroScope_2703_ = lean_ctor_get(v___x_2700_, 1);
v_ngen_2704_ = lean_ctor_get(v___x_2700_, 2);
v_auxDeclNGen_2705_ = lean_ctor_get(v___x_2700_, 3);
v_cache_2706_ = lean_ctor_get(v___x_2700_, 5);
v_recordedDeps_2707_ = lean_ctor_get(v___x_2700_, 6);
v_messages_2708_ = lean_ctor_get(v___x_2700_, 7);
v_infoState_2709_ = lean_ctor_get(v___x_2700_, 8);
v_snapshotTasks_2710_ = lean_ctor_get(v___x_2700_, 9);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2712_ = v___x_2700_;
v_isShared_2713_ = v_isSharedCheck_2740_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_snapshotTasks_2710_);
lean_inc(v_infoState_2709_);
lean_inc(v_messages_2708_);
lean_inc(v_recordedDeps_2707_);
lean_inc(v_cache_2706_);
lean_inc(v_traceState_2701_);
lean_inc(v_auxDeclNGen_2705_);
lean_inc(v_ngen_2704_);
lean_inc(v_nextMacroScope_2703_);
lean_inc(v_env_2702_);
lean_dec(v___x_2700_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2740_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
uint64_t v_tid_2714_; lean_object* v_traces_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2739_; 
v_tid_2714_ = lean_ctor_get_uint64(v_traceState_2701_, sizeof(void*)*1);
v_traces_2715_ = lean_ctor_get(v_traceState_2701_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_traceState_2701_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2717_ = v_traceState_2701_;
v_isShared_2718_ = v_isSharedCheck_2739_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_traces_2715_);
lean_dec(v_traceState_2701_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2739_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; double v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_box(0);
v___x_2721_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2722_ = 0;
v___x_2723_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2724_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2724_, 0, v_cls_2687_);
lean_ctor_set(v___x_2724_, 1, v___x_2720_);
lean_ctor_set(v___x_2724_, 2, v___x_2723_);
lean_ctor_set_float(v___x_2724_, sizeof(void*)*3, v___x_2721_);
lean_ctor_set_float(v___x_2724_, sizeof(void*)*3 + 8, v___x_2721_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*3 + 16, v___x_2722_);
v___x_2725_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2726_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v_a_2696_);
lean_ctor_set(v___x_2726_, 2, v___x_2725_);
lean_inc(v_ref_2694_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_ref_2694_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = l_Lean_PersistentArray_push___redArg(v_traces_2715_, v___x_2727_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2728_);
v___x_2730_ = v___x_2717_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2728_);
lean_ctor_set_uint64(v_reuseFailAlloc_2738_, sizeof(void*)*1, v_tid_2714_);
v___x_2730_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2732_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 4, v___x_2730_);
v___x_2732_ = v___x_2712_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_env_2702_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_nextMacroScope_2703_);
lean_ctor_set(v_reuseFailAlloc_2737_, 2, v_ngen_2704_);
lean_ctor_set(v_reuseFailAlloc_2737_, 3, v_auxDeclNGen_2705_);
lean_ctor_set(v_reuseFailAlloc_2737_, 4, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2737_, 5, v_cache_2706_);
lean_ctor_set(v_reuseFailAlloc_2737_, 6, v_recordedDeps_2707_);
lean_ctor_set(v_reuseFailAlloc_2737_, 7, v_messages_2708_);
lean_ctor_set(v_reuseFailAlloc_2737_, 8, v_infoState_2709_);
lean_ctor_set(v_reuseFailAlloc_2737_, 9, v_snapshotTasks_2710_);
v___x_2732_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = lean_st_ref_put(v___y_2692_, v___x_2732_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2719_);
v___x_2735_ = v___x_2698_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2719_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2742_, lean_object* v_msg_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2742_, v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2749_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2750_, lean_object* v_i_2751_, lean_object* v_k_2752_){
_start:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = lean_array_get_size(v_keys_2750_);
v___x_2754_ = lean_nat_dec_lt(v_i_2751_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_dec(v_i_2751_);
return v___x_2754_;
}
else
{
lean_object* v_k_x27_2755_; uint8_t v___x_2756_; 
v_k_x27_2755_ = lean_array_fget_borrowed(v_keys_2750_, v_i_2751_);
v___x_2756_ = l_Lean_instBEqExtraModUse_beq(v_k_2752_, v_k_x27_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_unsigned_to_nat(1u);
v___x_2758_ = lean_nat_add(v_i_2751_, v___x_2757_);
lean_dec(v_i_2751_);
v_i_2751_ = v___x_2758_;
goto _start;
}
else
{
lean_dec(v_i_2751_);
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2760_, lean_object* v_i_2761_, lean_object* v_k_2762_){
_start:
{
uint8_t v_res_2763_; lean_object* v_r_2764_; 
v_res_2763_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2760_, v_i_2761_, v_k_2762_);
lean_dec_ref(v_k_2762_);
lean_dec_ref(v_keys_2760_);
v_r_2764_ = lean_box(v_res_2763_);
return v_r_2764_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2765_, size_t v_x_2766_, lean_object* v_x_2767_){
_start:
{
if (lean_obj_tag(v_x_2765_) == 0)
{
lean_object* v_es_2768_; lean_object* v___x_2769_; size_t v___x_2770_; size_t v___x_2771_; lean_object* v_j_2772_; lean_object* v___x_2773_; 
v_es_2768_ = lean_ctor_get(v_x_2765_, 0);
v___x_2769_ = lean_box(2);
v___x_2770_ = ((size_t)31ULL);
v___x_2771_ = lean_usize_land(v_x_2766_, v___x_2770_);
v_j_2772_ = lean_usize_to_nat(v___x_2771_);
v___x_2773_ = lean_array_get_borrowed(v___x_2769_, v_es_2768_, v_j_2772_);
lean_dec(v_j_2772_);
switch(lean_obj_tag(v___x_2773_))
{
case 0:
{
lean_object* v_key_2774_; uint8_t v___x_2775_; 
v_key_2774_ = lean_ctor_get(v___x_2773_, 0);
v___x_2775_ = l_Lean_instBEqExtraModUse_beq(v_x_2767_, v_key_2774_);
return v___x_2775_;
}
case 1:
{
lean_object* v_node_2776_; size_t v___x_2777_; size_t v___x_2778_; 
v_node_2776_ = lean_ctor_get(v___x_2773_, 0);
v___x_2777_ = ((size_t)5ULL);
v___x_2778_ = lean_usize_shift_right(v_x_2766_, v___x_2777_);
v_x_2765_ = v_node_2776_;
v_x_2766_ = v___x_2778_;
goto _start;
}
default: 
{
uint8_t v___x_2780_; 
v___x_2780_ = 0;
return v___x_2780_;
}
}
}
else
{
lean_object* v_ks_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v_ks_2781_ = lean_ctor_get(v_x_2765_, 0);
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2781_, v___x_2782_, v_x_2767_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_){
_start:
{
size_t v_x_15695__boxed_2787_; uint8_t v_res_2788_; lean_object* v_r_2789_; 
v_x_15695__boxed_2787_ = lean_unbox_usize(v_x_2785_);
lean_dec(v_x_2785_);
v_res_2788_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2784_, v_x_15695__boxed_2787_, v_x_2786_);
lean_dec_ref(v_x_2786_);
lean_dec_ref(v_x_2784_);
v_r_2789_ = lean_box(v_res_2788_);
return v_r_2789_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2790_, lean_object* v_x_2791_){
_start:
{
uint64_t v___x_2792_; size_t v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = l_Lean_instHashableExtraModUse_hash(v_x_2791_);
v___x_2793_ = lean_uint64_to_usize(v___x_2792_);
v___x_2794_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2790_, v___x_2793_, v_x_2791_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2795_, lean_object* v_x_2796_){
_start:
{
uint8_t v_res_2797_; lean_object* v_r_2798_; 
v_res_2797_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2795_, v_x_2796_);
lean_dec_ref(v_x_2796_);
lean_dec_ref(v_x_2795_);
v_r_2798_ = lean_box(v_res_2797_);
return v_r_2798_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2799_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3));
v___x_2805_ = l_Lean_stringToMessageData(v___x_2804_);
return v___x_2805_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2808_ = l_Lean_stringToMessageData(v___x_2807_);
return v___x_2808_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2810_ = l_Lean_stringToMessageData(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_cls_2814_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_2815_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9));
v___x_2816_ = l_Lean_Name_append(v___x_2815_, v_cls_2814_);
return v___x_2816_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2822_ = l_Lean_stringToMessageData(v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2827_, uint8_t v_isMeta_2828_, lean_object* v_hint_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_env_2837_; uint8_t v_isExporting_2838_; lean_object* v_entry_2839_; lean_object* v___x_2840_; lean_object* v_env_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2835_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_2836_ = lean_st_ref_get(v___y_2833_);
v_env_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc_ref(v_env_2837_);
lean_dec(v___x_2836_);
v_isExporting_2838_ = lean_ctor_get_uint8(v_env_2837_, sizeof(void*)*8);
lean_dec_ref(v_env_2837_);
lean_inc(v_mod_2827_);
v_entry_2839_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2839_, 0, v_mod_2827_);
lean_ctor_set_uint8(v_entry_2839_, sizeof(void*)*1, v_isExporting_2838_);
lean_ctor_set_uint8(v_entry_2839_, sizeof(void*)*1 + 1, v_isMeta_2828_);
v___x_2840_ = lean_st_ref_get(v___y_2833_);
v_env_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc_ref(v_env_2841_);
lean_dec(v___x_2840_);
v___x_2842_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2843_ = lean_box(1);
v___x_2844_ = lean_box(0);
v___x_2888_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2835_, v___x_2842_, v_env_2841_, v___x_2843_, v___x_2844_);
v___x_2889_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2888_, v_entry_2839_);
lean_dec(v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v_toCold_2890_; lean_object* v_options_2891_; uint8_t v_hasTrace_2892_; 
v_toCold_2890_ = lean_ctor_get(v___y_2832_, 0);
v_options_2891_ = lean_ctor_get(v_toCold_2890_, 2);
v_hasTrace_2892_ = lean_ctor_get_uint8(v_options_2891_, sizeof(void*)*1);
if (v_hasTrace_2892_ == 0)
{
lean_dec(v_hint_2829_);
lean_dec(v_mod_2827_);
v___y_2846_ = v___y_2831_;
v___y_2847_ = v___y_2833_;
goto v___jp_2845_;
}
else
{
lean_object* v_inheritedTraceOptions_2893_; lean_object* v_cls_2894_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_inheritedTraceOptions_2893_ = lean_ctor_get(v_toCold_2890_, 11);
v_cls_2894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_2914_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_2915_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2893_, v_options_2891_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec(v_hint_2829_);
lean_dec(v_mod_2827_);
v___y_2846_ = v___y_2831_;
v___y_2847_ = v___y_2833_;
goto v___jp_2845_;
}
else
{
lean_object* v___x_2916_; lean_object* v___y_2918_; 
v___x_2916_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_2838_ == 0)
{
lean_object* v___x_2925_; 
v___x_2925_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2918_ = v___x_2925_;
goto v___jp_2917_;
}
else
{
lean_object* v___x_2926_; 
v___x_2926_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2918_ = v___x_2926_;
goto v___jp_2917_;
}
v___jp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_inc_ref(v___y_2918_);
v___x_2919_ = l_Lean_stringToMessageData(v___y_2918_);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2916_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
if (v_isMeta_2828_ == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_2901_ = v___x_2922_;
v___y_2902_ = v___x_2923_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2924_; 
v___x_2924_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_2901_ = v___x_2922_;
v___y_2902_ = v___x_2924_;
goto v___jp_2900_;
}
}
}
v___jp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___y_2896_);
lean_ctor_set(v___x_2898_, 1, v___y_2897_);
v___x_2899_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2894_, v___x_2898_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_dec_ref_known(v___x_2899_, 1);
v___y_2846_ = v___y_2831_;
v___y_2847_ = v___y_2833_;
goto v___jp_2845_;
}
else
{
lean_dec_ref_known(v_entry_2839_, 1);
return v___x_2899_;
}
}
v___jp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
lean_inc_ref(v___y_2902_);
v___x_2903_ = l_Lean_stringToMessageData(v___y_2902_);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___y_2901_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_MessageData_ofName(v_mod_2827_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = l_Lean_Name_isAnonymous(v_hint_2829_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2911_ = l_Lean_MessageData_ofName(v_hint_2829_);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___y_2896_ = v___x_2908_;
v___y_2897_ = v___x_2912_;
goto v___jp_2895_;
}
else
{
lean_object* v___x_2913_; 
lean_dec(v_hint_2829_);
v___x_2913_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_2896_ = v___x_2908_;
v___y_2897_ = v___x_2913_;
goto v___jp_2895_;
}
}
}
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec_ref_known(v_entry_2839_, 1);
lean_dec(v_hint_2829_);
lean_dec(v_mod_2827_);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
v___jp_2845_:
{
lean_object* v___x_2848_; lean_object* v_toEnvExtension_2849_; lean_object* v_env_2850_; lean_object* v_nextMacroScope_2851_; lean_object* v_ngen_2852_; lean_object* v_auxDeclNGen_2853_; lean_object* v_traceState_2854_; lean_object* v_recordedDeps_2855_; lean_object* v_messages_2856_; lean_object* v_infoState_2857_; lean_object* v_snapshotTasks_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2886_; 
v___x_2848_ = lean_st_ref_take(v___y_2847_);
v_toEnvExtension_2849_ = lean_ctor_get(v___x_2842_, 0);
v_env_2850_ = lean_ctor_get(v___x_2848_, 0);
v_nextMacroScope_2851_ = lean_ctor_get(v___x_2848_, 1);
v_ngen_2852_ = lean_ctor_get(v___x_2848_, 2);
v_auxDeclNGen_2853_ = lean_ctor_get(v___x_2848_, 3);
v_traceState_2854_ = lean_ctor_get(v___x_2848_, 4);
v_recordedDeps_2855_ = lean_ctor_get(v___x_2848_, 6);
v_messages_2856_ = lean_ctor_get(v___x_2848_, 7);
v_infoState_2857_ = lean_ctor_get(v___x_2848_, 8);
v_snapshotTasks_2858_ = lean_ctor_get(v___x_2848_, 9);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2848_, 5);
lean_dec(v_unused_2887_);
v___x_2860_ = v___x_2848_;
v_isShared_2861_ = v_isSharedCheck_2886_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_snapshotTasks_2858_);
lean_inc(v_infoState_2857_);
lean_inc(v_messages_2856_);
lean_inc(v_recordedDeps_2855_);
lean_inc(v_traceState_2854_);
lean_inc(v_auxDeclNGen_2853_);
lean_inc(v_ngen_2852_);
lean_inc(v_nextMacroScope_2851_);
lean_inc(v_env_2850_);
lean_dec(v___x_2848_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2886_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_asyncMode_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v_asyncMode_2862_ = lean_ctor_get(v_toEnvExtension_2849_, 2);
v___x_2863_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2842_, v_env_2850_, v_entry_2839_, v_asyncMode_2862_, v___x_2844_);
v___x_2864_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 5, v___x_2864_);
lean_ctor_set(v___x_2860_, 0, v___x_2863_);
v___x_2866_ = v___x_2860_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_nextMacroScope_2851_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_ngen_2852_);
lean_ctor_set(v_reuseFailAlloc_2885_, 3, v_auxDeclNGen_2853_);
lean_ctor_set(v_reuseFailAlloc_2885_, 4, v_traceState_2854_);
lean_ctor_set(v_reuseFailAlloc_2885_, 5, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2885_, 6, v_recordedDeps_2855_);
lean_ctor_set(v_reuseFailAlloc_2885_, 7, v_messages_2856_);
lean_ctor_set(v_reuseFailAlloc_2885_, 8, v_infoState_2857_);
lean_ctor_set(v_reuseFailAlloc_2885_, 9, v_snapshotTasks_2858_);
v___x_2866_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v_mctx_2869_; lean_object* v_zetaDeltaFVarIds_2870_; lean_object* v_postponed_2871_; lean_object* v_diag_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2883_; 
v___x_2867_ = lean_st_ref_put(v___y_2847_, v___x_2866_);
v___x_2868_ = lean_st_ref_take(v___y_2846_);
v_mctx_2869_ = lean_ctor_get(v___x_2868_, 0);
v_zetaDeltaFVarIds_2870_ = lean_ctor_get(v___x_2868_, 2);
v_postponed_2871_ = lean_ctor_get(v___x_2868_, 3);
v_diag_2872_ = lean_ctor_get(v___x_2868_, 4);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v___x_2868_, 1);
lean_dec(v_unused_2884_);
v___x_2874_ = v___x_2868_;
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_diag_2872_);
lean_inc(v_postponed_2871_);
lean_inc(v_zetaDeltaFVarIds_2870_);
lean_inc(v_mctx_2869_);
lean_dec(v___x_2868_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2877_);
v___x_2879_ = v___x_2874_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_mctx_2869_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_zetaDeltaFVarIds_2870_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_postponed_2871_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v_diag_2872_);
v___x_2879_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_st_ref_put(v___y_2846_, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2876_);
return v___x_2881_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2929_, lean_object* v_isMeta_2930_, lean_object* v_hint_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v_isMeta_boxed_2937_; lean_object* v_res_2938_; 
v_isMeta_boxed_2937_ = lean_unbox(v_isMeta_2930_);
v_res_2938_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2929_, v_isMeta_boxed_2937_, v_hint_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2939_, lean_object* v_x_2940_){
_start:
{
if (lean_obj_tag(v_x_2940_) == 0)
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_box(0);
return v___x_2941_;
}
else
{
lean_object* v_key_2942_; lean_object* v_value_2943_; lean_object* v_tail_2944_; uint8_t v___x_2945_; 
v_key_2942_ = lean_ctor_get(v_x_2940_, 0);
v_value_2943_ = lean_ctor_get(v_x_2940_, 1);
v_tail_2944_ = lean_ctor_get(v_x_2940_, 2);
v___x_2945_ = lean_name_eq(v_key_2942_, v_a_2939_);
if (v___x_2945_ == 0)
{
v_x_2940_ = v_tail_2944_;
goto _start;
}
else
{
lean_object* v___x_2947_; 
lean_inc(v_value_2943_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_value_2943_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2948_, lean_object* v_x_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2948_, v_x_2949_);
lean_dec(v_x_2949_);
lean_dec(v_a_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_buckets_2953_; lean_object* v___x_2954_; uint64_t v___y_2956_; 
v_buckets_2953_ = lean_ctor_get(v_m_2951_, 1);
v___x_2954_ = lean_array_get_size(v_buckets_2953_);
if (lean_obj_tag(v_a_2952_) == 0)
{
uint64_t v___x_2970_; 
v___x_2970_ = 1723ULL;
v___y_2956_ = v___x_2970_;
goto v___jp_2955_;
}
else
{
uint64_t v_hash_2971_; 
v_hash_2971_ = lean_ctor_get_uint64(v_a_2952_, sizeof(void*)*2);
v___y_2956_ = v_hash_2971_;
goto v___jp_2955_;
}
v___jp_2955_:
{
uint64_t v___x_2957_; uint64_t v___x_2958_; uint64_t v_fold_2959_; uint64_t v___x_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; size_t v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2957_ = 32ULL;
v___x_2958_ = lean_uint64_shift_right(v___y_2956_, v___x_2957_);
v_fold_2959_ = lean_uint64_xor(v___y_2956_, v___x_2958_);
v___x_2960_ = 16ULL;
v___x_2961_ = lean_uint64_shift_right(v_fold_2959_, v___x_2960_);
v___x_2962_ = lean_uint64_xor(v_fold_2959_, v___x_2961_);
v___x_2963_ = lean_uint64_to_usize(v___x_2962_);
v___x_2964_ = lean_usize_of_nat(v___x_2954_);
v___x_2965_ = ((size_t)1ULL);
v___x_2966_ = lean_usize_sub(v___x_2964_, v___x_2965_);
v___x_2967_ = lean_usize_land(v___x_2963_, v___x_2966_);
v___x_2968_ = lean_array_uget_borrowed(v_buckets_2953_, v___x_2967_);
v___x_2969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2952_, v___x_2968_);
return v___x_2969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2972_, v_a_2973_);
lean_dec(v_a_2973_);
lean_dec_ref(v_m_2972_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2975_, lean_object* v_declName_2976_, lean_object* v_as_2977_, size_t v_sz_2978_, size_t v_i_2979_, lean_object* v_b_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
uint8_t v___x_2986_; 
v___x_2986_ = lean_usize_dec_lt(v_i_2979_, v_sz_2978_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; 
lean_dec(v_declName_2976_);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_b_2980_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v_modules_2989_; lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v___x_2992_; lean_object* v_toImport_2993_; lean_object* v_module_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2988_ = l_Lean_Environment_header(v___x_2975_);
v_modules_2989_ = lean_ctor_get(v___x_2988_, 3);
lean_inc_ref(v_modules_2989_);
lean_dec_ref(v___x_2988_);
v___x_2990_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2991_ = lean_array_uget_borrowed(v_as_2977_, v_i_2979_);
v___x_2992_ = lean_array_get(v___x_2990_, v_modules_2989_, v_a_2991_);
lean_dec_ref(v_modules_2989_);
v_toImport_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc_ref(v_toImport_2993_);
lean_dec(v___x_2992_);
v_module_2994_ = lean_ctor_get(v_toImport_2993_, 0);
lean_inc(v_module_2994_);
lean_dec_ref(v_toImport_2993_);
v___x_2995_ = lean_box(0);
v___x_2996_ = 0;
lean_inc(v_declName_2976_);
v___x_2997_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_2994_, v___x_2996_, v_declName_2976_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
if (lean_obj_tag(v___x_2997_) == 0)
{
size_t v___x_2998_; size_t v___x_2999_; 
lean_dec_ref_known(v___x_2997_, 1);
v___x_2998_ = ((size_t)1ULL);
v___x_2999_ = lean_usize_add(v_i_2979_, v___x_2998_);
v_i_2979_ = v___x_2999_;
v_b_2980_ = v___x_2995_;
goto _start;
}
else
{
lean_dec(v_declName_2976_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_3001_, lean_object* v_declName_3002_, lean_object* v_as_3003_, lean_object* v_sz_3004_, lean_object* v_i_3005_, lean_object* v_b_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
size_t v_sz_boxed_3012_; size_t v_i_boxed_3013_; lean_object* v_res_3014_; 
v_sz_boxed_3012_ = lean_unbox_usize(v_sz_3004_);
lean_dec(v_sz_3004_);
v_i_boxed_3013_ = lean_unbox_usize(v_i_3005_);
lean_dec(v_i_3005_);
v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3001_, v_declName_3002_, v_as_3003_, v_sz_boxed_3012_, v_i_boxed_3013_, v_b_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v_as_3003_);
lean_dec_ref(v___x_3001_);
return v_res_3014_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3018_, uint8_t v_isMeta_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_env_3030_; lean_object* v___y_3032_; lean_object* v___x_3045_; 
v___x_3025_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3026_ = lean_st_ref_get(v___y_3023_);
v_env_3030_ = lean_ctor_get(v___x_3026_, 0);
lean_inc_ref(v_env_3030_);
lean_dec(v___x_3026_);
v___x_3045_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3030_, v_declName_3018_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_dec_ref(v_env_3030_);
lean_dec(v_declName_3018_);
goto v___jp_3027_;
}
else
{
lean_object* v_val_3046_; lean_object* v___x_3047_; lean_object* v_modules_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v_val_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_val_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = l_Lean_Environment_header(v_env_3030_);
v_modules_3048_ = lean_ctor_get(v___x_3047_, 3);
lean_inc_ref(v_modules_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = lean_array_get_size(v_modules_3048_);
v___x_3050_ = lean_nat_dec_lt(v_val_3046_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_dec_ref(v_modules_3048_);
lean_dec(v_val_3046_);
lean_dec_ref(v_env_3030_);
lean_dec(v_declName_3018_);
goto v___jp_3027_;
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___y_3054_; 
v___x_3051_ = lean_array_fget(v_modules_3048_, v_val_3046_);
lean_dec(v_val_3046_);
lean_dec_ref(v_modules_3048_);
v___x_3052_ = lean_st_ref_get(v___y_3023_);
if (v_isMeta_3019_ == 0)
{
lean_dec(v___x_3052_);
v___y_3054_ = v_isMeta_3019_;
goto v___jp_3053_;
}
else
{
lean_object* v_env_3065_; uint8_t v___x_3066_; 
v_env_3065_ = lean_ctor_get(v___x_3052_, 0);
lean_inc_ref(v_env_3065_);
lean_dec(v___x_3052_);
lean_inc(v_declName_3018_);
v___x_3066_ = l_Lean_isMarkedMeta(v_env_3065_, v_declName_3018_);
if (v___x_3066_ == 0)
{
v___y_3054_ = v_isMeta_3019_;
goto v___jp_3053_;
}
else
{
uint8_t v___x_3067_; 
v___x_3067_ = 0;
v___y_3054_ = v___x_3067_;
goto v___jp_3053_;
}
}
v___jp_3053_:
{
lean_object* v_toImport_3055_; lean_object* v_module_3056_; lean_object* v___x_3057_; 
v_toImport_3055_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_ref(v_toImport_3055_);
lean_dec(v___x_3051_);
v_module_3056_ = lean_ctor_get(v_toImport_3055_, 0);
lean_inc(v_module_3056_);
lean_dec_ref(v_toImport_3055_);
lean_inc(v_declName_3018_);
v___x_3057_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3056_, v___y_3054_, v_declName_3018_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec_ref_known(v___x_3057_, 1);
v___x_3058_ = l_Lean_indirectModUseExt;
v___x_3059_ = lean_box(1);
v___x_3060_ = lean_box(0);
lean_inc_ref(v_env_3030_);
v___x_3061_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3025_, v___x_3058_, v_env_3030_, v___x_3059_, v___x_3060_);
v___x_3062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3061_, v_declName_3018_);
lean_dec(v___x_3061_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3032_ = v___x_3063_;
goto v___jp_3031_;
}
else
{
lean_object* v_val_3064_; 
v_val_3064_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_val_3064_);
lean_dec_ref_known(v___x_3062_, 1);
v___y_3032_ = v_val_3064_;
goto v___jp_3031_;
}
}
else
{
lean_dec_ref(v_env_3030_);
lean_dec(v_declName_3018_);
return v___x_3057_;
}
}
}
}
v___jp_3027_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
v___jp_3031_:
{
lean_object* v___x_3033_; size_t v_sz_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v___x_3033_ = lean_box(0);
v_sz_3034_ = lean_array_size(v___y_3032_);
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3030_, v_declName_3018_, v___y_3032_, v_sz_3034_, v___x_3035_, v___x_3033_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v_env_3030_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; 
v_unused_3044_ = lean_ctor_get(v___x_3036_, 0);
lean_dec(v_unused_3044_);
v___x_3038_ = v___x_3036_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_dec(v___x_3036_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3033_);
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3033_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
return v___x_3036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3068_, lean_object* v_isMeta_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
uint8_t v_isMeta_boxed_3075_; lean_object* v_res_3076_; 
v_isMeta_boxed_3075_ = lean_unbox(v_isMeta_3069_);
v_res_3076_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3068_, v_isMeta_boxed_3075_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3077_, uint8_t v_isExporting_3078_, lean_object* v___x_3079_, lean_object* v___y_3080_, lean_object* v___x_3081_, lean_object* v_a_x3f_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v_env_3085_; lean_object* v_nextMacroScope_3086_; lean_object* v_ngen_3087_; lean_object* v_auxDeclNGen_3088_; lean_object* v_traceState_3089_; lean_object* v_recordedDeps_3090_; lean_object* v_messages_3091_; lean_object* v_infoState_3092_; lean_object* v_snapshotTasks_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3118_; 
v___x_3084_ = lean_st_ref_take(v___y_3077_);
v_env_3085_ = lean_ctor_get(v___x_3084_, 0);
v_nextMacroScope_3086_ = lean_ctor_get(v___x_3084_, 1);
v_ngen_3087_ = lean_ctor_get(v___x_3084_, 2);
v_auxDeclNGen_3088_ = lean_ctor_get(v___x_3084_, 3);
v_traceState_3089_ = lean_ctor_get(v___x_3084_, 4);
v_recordedDeps_3090_ = lean_ctor_get(v___x_3084_, 6);
v_messages_3091_ = lean_ctor_get(v___x_3084_, 7);
v_infoState_3092_ = lean_ctor_get(v___x_3084_, 8);
v_snapshotTasks_3093_ = lean_ctor_get(v___x_3084_, 9);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v___x_3084_, 5);
lean_dec(v_unused_3119_);
v___x_3095_ = v___x_3084_;
v_isShared_3096_ = v_isSharedCheck_3118_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_snapshotTasks_3093_);
lean_inc(v_infoState_3092_);
lean_inc(v_messages_3091_);
lean_inc(v_recordedDeps_3090_);
lean_inc(v_traceState_3089_);
lean_inc(v_auxDeclNGen_3088_);
lean_inc(v_ngen_3087_);
lean_inc(v_nextMacroScope_3086_);
lean_inc(v_env_3085_);
lean_dec(v___x_3084_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3118_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = l_Lean_Environment_setExporting(v_env_3085_, v_isExporting_3078_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 5, v___x_3079_);
lean_ctor_set(v___x_3095_, 0, v___x_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_nextMacroScope_3086_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_ngen_3087_);
lean_ctor_set(v_reuseFailAlloc_3117_, 3, v_auxDeclNGen_3088_);
lean_ctor_set(v_reuseFailAlloc_3117_, 4, v_traceState_3089_);
lean_ctor_set(v_reuseFailAlloc_3117_, 5, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3117_, 6, v_recordedDeps_3090_);
lean_ctor_set(v_reuseFailAlloc_3117_, 7, v_messages_3091_);
lean_ctor_set(v_reuseFailAlloc_3117_, 8, v_infoState_3092_);
lean_ctor_set(v_reuseFailAlloc_3117_, 9, v_snapshotTasks_3093_);
v___x_3099_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v_mctx_3102_; lean_object* v_zetaDeltaFVarIds_3103_; lean_object* v_postponed_3104_; lean_object* v_diag_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3115_; 
v___x_3100_ = lean_st_ref_put(v___y_3077_, v___x_3099_);
v___x_3101_ = lean_st_ref_take(v___y_3080_);
v_mctx_3102_ = lean_ctor_get(v___x_3101_, 0);
v_zetaDeltaFVarIds_3103_ = lean_ctor_get(v___x_3101_, 2);
v_postponed_3104_ = lean_ctor_get(v___x_3101_, 3);
v_diag_3105_ = lean_ctor_get(v___x_3101_, 4);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3101_, 1);
lean_dec(v_unused_3116_);
v___x_3107_ = v___x_3101_;
v_isShared_3108_ = v_isSharedCheck_3115_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_diag_3105_);
lean_inc(v_postponed_3104_);
lean_inc(v_zetaDeltaFVarIds_3103_);
lean_inc(v_mctx_3102_);
lean_dec(v___x_3101_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3115_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_box(0);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v___x_3081_);
v___x_3111_ = v___x_3107_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_mctx_3102_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_zetaDeltaFVarIds_3103_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_postponed_3104_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_diag_3105_);
v___x_3111_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_st_ref_put(v___y_3080_, v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3109_);
return v___x_3113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3120_, lean_object* v_isExporting_3121_, lean_object* v___x_3122_, lean_object* v___y_3123_, lean_object* v___x_3124_, lean_object* v_a_x3f_3125_, lean_object* v___y_3126_){
_start:
{
uint8_t v_isExporting_boxed_3127_; lean_object* v_res_3128_; 
v_isExporting_boxed_3127_ = lean_unbox(v_isExporting_3121_);
v_res_3128_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3120_, v_isExporting_boxed_3127_, v___x_3122_, v___y_3123_, v___x_3124_, v_a_x3f_3125_);
lean_dec(v_a_x3f_3125_);
lean_dec(v___y_3123_);
lean_dec(v___y_3120_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3129_, uint8_t v_isExporting_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; lean_object* v_env_3137_; lean_object* v___x_3138_; uint8_t v_isModule_3139_; 
v___x_3136_ = lean_st_ref_get(v___y_3134_);
v_env_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc_ref(v_env_3137_);
lean_dec(v___x_3136_);
v___x_3138_ = l_Lean_Environment_header(v_env_3137_);
v_isModule_3139_ = lean_ctor_get_uint8(v___x_3138_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3138_);
if (v_isModule_3139_ == 0)
{
lean_object* v___x_3140_; 
lean_dec_ref(v_env_3137_);
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
lean_inc_ref(v___y_3131_);
v___x_3140_ = lean_apply_5(v_x_3129_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, lean_box(0));
return v___x_3140_;
}
else
{
uint8_t v_isExporting_3141_; 
v_isExporting_3141_ = lean_ctor_get_uint8(v_env_3137_, sizeof(void*)*8);
lean_dec_ref(v_env_3137_);
if (v_isExporting_3130_ == 0)
{
if (v_isExporting_3141_ == 0)
{
lean_object* v___x_3208_; 
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
lean_inc_ref(v___y_3131_);
v___x_3208_ = lean_apply_5(v_x_3129_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, lean_box(0));
return v___x_3208_;
}
else
{
goto v___jp_3142_;
}
}
else
{
if (v_isExporting_3141_ == 0)
{
goto v___jp_3142_;
}
else
{
lean_object* v___x_3209_; 
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
lean_inc_ref(v___y_3131_);
v___x_3209_ = lean_apply_5(v_x_3129_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, lean_box(0));
return v___x_3209_;
}
}
v___jp_3142_:
{
lean_object* v___x_3143_; lean_object* v_env_3144_; lean_object* v_nextMacroScope_3145_; lean_object* v_ngen_3146_; lean_object* v_auxDeclNGen_3147_; lean_object* v_traceState_3148_; lean_object* v_recordedDeps_3149_; lean_object* v_messages_3150_; lean_object* v_infoState_3151_; lean_object* v_snapshotTasks_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3206_; 
v___x_3143_ = lean_st_ref_take(v___y_3134_);
v_env_3144_ = lean_ctor_get(v___x_3143_, 0);
v_nextMacroScope_3145_ = lean_ctor_get(v___x_3143_, 1);
v_ngen_3146_ = lean_ctor_get(v___x_3143_, 2);
v_auxDeclNGen_3147_ = lean_ctor_get(v___x_3143_, 3);
v_traceState_3148_ = lean_ctor_get(v___x_3143_, 4);
v_recordedDeps_3149_ = lean_ctor_get(v___x_3143_, 6);
v_messages_3150_ = lean_ctor_get(v___x_3143_, 7);
v_infoState_3151_ = lean_ctor_get(v___x_3143_, 8);
v_snapshotTasks_3152_ = lean_ctor_get(v___x_3143_, 9);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3143_, 5);
lean_dec(v_unused_3207_);
v___x_3154_ = v___x_3143_;
v_isShared_3155_ = v_isSharedCheck_3206_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snapshotTasks_3152_);
lean_inc(v_infoState_3151_);
lean_inc(v_messages_3150_);
lean_inc(v_recordedDeps_3149_);
lean_inc(v_traceState_3148_);
lean_inc(v_auxDeclNGen_3147_);
lean_inc(v_ngen_3146_);
lean_inc(v_nextMacroScope_3145_);
lean_inc(v_env_3144_);
lean_dec(v___x_3143_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3206_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3156_ = l_Lean_Environment_setExporting(v_env_3144_, v_isExporting_3130_);
v___x_3157_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 5, v___x_3157_);
lean_ctor_set(v___x_3154_, 0, v___x_3156_);
v___x_3159_ = v___x_3154_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_nextMacroScope_3145_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_ngen_3146_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v_auxDeclNGen_3147_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v_traceState_3148_);
lean_ctor_set(v_reuseFailAlloc_3205_, 5, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3205_, 6, v_recordedDeps_3149_);
lean_ctor_set(v_reuseFailAlloc_3205_, 7, v_messages_3150_);
lean_ctor_set(v_reuseFailAlloc_3205_, 8, v_infoState_3151_);
lean_ctor_set(v_reuseFailAlloc_3205_, 9, v_snapshotTasks_3152_);
v___x_3159_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v_mctx_3162_; lean_object* v_zetaDeltaFVarIds_3163_; lean_object* v_postponed_3164_; lean_object* v_diag_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3203_; 
v___x_3160_ = lean_st_ref_put(v___y_3134_, v___x_3159_);
v___x_3161_ = lean_st_ref_take(v___y_3132_);
v_mctx_3162_ = lean_ctor_get(v___x_3161_, 0);
v_zetaDeltaFVarIds_3163_ = lean_ctor_get(v___x_3161_, 2);
v_postponed_3164_ = lean_ctor_get(v___x_3161_, 3);
v_diag_3165_ = lean_ctor_get(v___x_3161_, 4);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v___x_3161_, 1);
lean_dec(v_unused_3204_);
v___x_3167_ = v___x_3161_;
v_isShared_3168_ = v_isSharedCheck_3203_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_diag_3165_);
lean_inc(v_postponed_3164_);
lean_inc(v_zetaDeltaFVarIds_3163_);
lean_inc(v_mctx_3162_);
lean_dec(v___x_3161_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3203_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___x_3169_);
v___x_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_mctx_3162_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_zetaDeltaFVarIds_3163_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v_postponed_3164_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v_diag_3165_);
v___x_3171_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v_r_3173_; 
v___x_3172_ = lean_st_ref_put(v___y_3132_, v___x_3171_);
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
lean_inc_ref(v___y_3131_);
v_r_3173_ = lean_apply_5(v_x_3129_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, lean_box(0));
if (lean_obj_tag(v_r_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3190_; 
v_a_3174_ = lean_ctor_get(v_r_3173_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_r_3173_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3176_ = v_r_3173_;
v_isShared_3177_ = v_isSharedCheck_3190_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v_r_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3190_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
lean_inc(v_a_3174_);
if (v_isShared_3177_ == 0)
{
lean_ctor_set_tag(v___x_3176_, 1);
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
v___x_3180_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3134_, v_isExporting_3141_, v___x_3157_, v___y_3132_, v___x_3169_, v___x_3179_);
lean_dec_ref(v___x_3179_);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3187_ == 0)
{
lean_object* v_unused_3188_; 
v_unused_3188_ = lean_ctor_get(v___x_3180_, 0);
lean_dec(v_unused_3188_);
v___x_3182_ = v___x_3180_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_dec(v___x_3180_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v_a_3174_);
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3174_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
v_a_3191_ = lean_ctor_get(v_r_3173_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v_r_3173_, 1);
v___x_3192_ = lean_box(0);
v___x_3193_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3134_, v_isExporting_3141_, v___x_3157_, v___y_3132_, v___x_3169_, v___x_3192_);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v___x_3193_, 0);
lean_dec(v_unused_3201_);
v___x_3195_ = v___x_3193_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_dec(v___x_3193_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set_tag(v___x_3195_, 1);
lean_ctor_set(v___x_3195_, 0, v_a_3191_);
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3191_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3210_, lean_object* v_isExporting_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
uint8_t v_isExporting_boxed_3217_; lean_object* v_res_3218_; 
v_isExporting_boxed_3217_ = lean_unbox(v_isExporting_3211_);
v_res_3218_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3210_, v_isExporting_boxed_3217_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3219_, uint8_t v_when_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
if (v_when_3220_ == 0)
{
lean_object* v___x_3226_; 
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
v___x_3226_ = lean_apply_5(v_x_3219_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, lean_box(0));
return v___x_3226_;
}
else
{
uint8_t v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = 0;
v___x_3228_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3219_, v___x_3227_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
return v___x_3228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3229_, lean_object* v_when_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
uint8_t v_when_boxed_3236_; lean_object* v_res_3237_; 
v_when_boxed_3236_ = lean_unbox(v_when_3230_);
v_res_3237_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3229_, v_when_boxed_3236_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_3238_, uint8_t v_showInfo_3239_, uint8_t v_minIndexable_3240_, lean_object* v_attrName_3241_, lean_object* v___x_3242_, lean_object* v_declName_3243_, lean_object* v_stx_3244_, uint8_t v_attrKind_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___f_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___y_3271_; lean_object* v___x_3281_; 
v___x_3249_ = 0;
v___x_3250_ = lean_box(v___x_3249_);
v___x_3251_ = lean_box(v_attrKind_3245_);
v___x_3252_ = lean_box(v_showInfo_3239_);
v___x_3253_ = lean_box(v_minIndexable_3240_);
lean_inc(v_declName_3243_);
v___f_3254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3254_, 0, v_declName_3243_);
lean_closure_set(v___f_3254_, 1, v___x_3250_);
lean_closure_set(v___f_3254_, 2, v___x_3251_);
lean_closure_set(v___f_3254_, 3, v_stx_3244_);
lean_closure_set(v___f_3254_, 4, v_ext_3238_);
lean_closure_set(v___f_3254_, 5, v___x_3252_);
lean_closure_set(v___f_3254_, 6, v___x_3253_);
lean_closure_set(v___f_3254_, 7, v_attrName_3241_);
v___x_3255_ = 1;
v___x_3256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3257_ = lean_unsigned_to_nat(32u);
v___x_3258_ = lean_mk_empty_array_with_capacity(v___x_3257_);
lean_dec_ref(v___x_3258_);
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3263_ = lean_box(0);
lean_inc(v___x_3242_);
v___x_3264_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3264_, 0, v___x_3256_);
lean_ctor_set(v___x_3264_, 1, v___x_3242_);
lean_ctor_set(v___x_3264_, 2, v___x_3261_);
lean_ctor_set(v___x_3264_, 3, v___x_3262_);
lean_ctor_set(v___x_3264_, 4, v___x_3263_);
lean_ctor_set(v___x_3264_, 5, v___x_3259_);
lean_ctor_set(v___x_3264_, 6, v___x_3263_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7, v___x_3249_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 1, v___x_3249_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 2, v___x_3249_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*7 + 3, v___x_3255_);
v___x_3265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3265_);
lean_ctor_set(v___x_3268_, 1, v___x_3266_);
lean_ctor_set(v___x_3268_, 2, v___x_3242_);
lean_ctor_set(v___x_3268_, 3, v___x_3260_);
lean_ctor_set(v___x_3268_, 4, v___x_3267_);
v___x_3269_ = lean_st_mk_ref(v___x_3268_);
v___x_3281_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3243_, v___x_3249_, v___x_3264_, v___x_3269_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v___x_3282_; 
lean_dec_ref_known(v___x_3281_, 1);
v___x_3282_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3254_, v___x_3255_, v___x_3264_, v___x_3269_, v___y_3246_, v___y_3247_);
lean_dec_ref_known(v___x_3264_, 7);
v___y_3271_ = v___x_3282_;
goto v___jp_3270_;
}
else
{
lean_dec_ref_known(v___x_3264_, 7);
lean_dec_ref(v___f_3254_);
v___y_3271_ = v___x_3281_;
goto v___jp_3270_;
}
v___jp_3270_:
{
if (lean_obj_tag(v___y_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
v_a_3272_ = lean_ctor_get(v___y_3271_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___y_3271_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3274_ = v___y_3271_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___y_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = lean_st_ref_get(v___x_3269_);
lean_dec(v___x_3269_);
lean_dec(v___x_3276_);
if (v_isShared_3275_ == 0)
{
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3272_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_dec(v___x_3269_);
return v___y_3271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_3283_, lean_object* v_showInfo_3284_, lean_object* v_minIndexable_3285_, lean_object* v_attrName_3286_, lean_object* v___x_3287_, lean_object* v_declName_3288_, lean_object* v_stx_3289_, lean_object* v_attrKind_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v_showInfo_boxed_3294_; uint8_t v_minIndexable_boxed_3295_; uint8_t v_attrKind_boxed_3296_; lean_object* v_res_3297_; 
v_showInfo_boxed_3294_ = lean_unbox(v_showInfo_3284_);
v_minIndexable_boxed_3295_ = lean_unbox(v_minIndexable_3285_);
v_attrKind_boxed_3296_ = lean_unbox(v_attrKind_3290_);
v_res_3297_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_3283_, v_showInfo_boxed_3294_, v_minIndexable_boxed_3295_, v_attrName_3286_, v___x_3287_, v_declName_3288_, v_stx_3289_, v_attrKind_boxed_3296_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3320_, uint8_t v_minIndexable_3321_, uint8_t v_showInfo_3322_, lean_object* v_ext_3323_, lean_object* v_ref_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___f_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___f_3331_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3377_; 
v___x_3326_ = lean_box(1);
v___x_3327_ = lean_box(v_showInfo_3322_);
lean_inc_n(v_attrName_3320_, 2);
lean_inc_ref(v_ext_3323_);
v___f_3328_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3328_, 0, v_ext_3323_);
lean_closure_set(v___f_3328_, 1, v___x_3326_);
lean_closure_set(v___f_3328_, 2, v___x_3327_);
lean_closure_set(v___f_3328_, 3, v_attrName_3320_);
v___x_3329_ = lean_box(v_showInfo_3322_);
v___x_3330_ = lean_box(v_minIndexable_3321_);
v___f_3331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3331_, 0, v_ext_3323_);
lean_closure_set(v___f_3331_, 1, v___x_3329_);
lean_closure_set(v___f_3331_, 2, v___x_3330_);
lean_closure_set(v___f_3331_, 3, v_attrName_3320_);
lean_closure_set(v___f_3331_, 4, v___x_3326_);
if (v_minIndexable_3321_ == 0)
{
if (v_showInfo_3322_ == 0)
{
lean_inc(v_attrName_3320_);
v___y_3377_ = v_attrName_3320_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3320_);
v___x_3406_ = lean_name_append_after(v_attrName_3320_, v___x_3405_);
v___y_3377_ = v___x_3406_;
goto v___jp_3376_;
}
}
else
{
if (v_showInfo_3322_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3320_);
v___x_3408_ = lean_name_append_after(v_attrName_3320_, v___x_3407_);
v___y_3377_ = v___x_3408_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3320_);
v___x_3410_ = lean_name_append_after(v_attrName_3320_, v___x_3409_);
v___y_3377_ = v___x_3410_;
goto v___jp_3376_;
}
}
v___jp_3332_:
{
lean_object* v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3336_ = 1;
v___x_3337_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3320_, v___x_3336_);
v___x_3338_ = lean_string_append(v___x_3335_, v___x_3337_);
v___x_3339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3340_ = lean_string_append(v___x_3338_, v___x_3339_);
v___x_3341_ = lean_string_append(v___x_3340_, v___x_3337_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
v___x_3344_ = lean_string_append(v___x_3343_, v___x_3337_);
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3346_ = lean_string_append(v___x_3344_, v___x_3345_);
v___x_3347_ = lean_string_append(v___x_3346_, v___x_3337_);
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3349_ = lean_string_append(v___x_3347_, v___x_3348_);
v___x_3350_ = lean_string_append(v___x_3349_, v___x_3337_);
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3352_ = lean_string_append(v___x_3350_, v___x_3351_);
v___x_3353_ = lean_string_append(v___x_3352_, v___x_3337_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3355_ = lean_string_append(v___x_3353_, v___x_3354_);
v___x_3356_ = lean_string_append(v___x_3355_, v___x_3337_);
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3358_ = lean_string_append(v___x_3356_, v___x_3357_);
v___x_3359_ = lean_string_append(v___x_3358_, v___x_3337_);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3361_ = lean_string_append(v___x_3359_, v___x_3360_);
v___x_3362_ = lean_string_append(v___x_3361_, v___x_3337_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
v___x_3365_ = lean_string_append(v___x_3364_, v___x_3337_);
v___x_3366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3367_ = lean_string_append(v___x_3365_, v___x_3366_);
v___x_3368_ = lean_string_append(v___x_3367_, v___x_3337_);
lean_dec_ref(v___x_3337_);
v___x_3369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3370_ = lean_string_append(v___x_3368_, v___x_3369_);
v___x_3371_ = lean_string_append(v___y_3334_, v___x_3370_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = 1;
v___x_3373_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3373_, 0, v_ref_3324_);
lean_ctor_set(v___x_3373_, 1, v___y_3333_);
lean_ctor_set(v___x_3373_, 2, v___x_3371_);
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*3, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___f_3331_);
lean_ctor_set(v___x_3374_, 2, v___f_3328_);
v___x_3375_ = l_Lean_registerBuiltinAttribute(v___x_3374_);
return v___x_3375_;
}
v___jp_3376_:
{
if (v_minIndexable_3321_ == 0)
{
if (v_showInfo_3322_ == 0)
{
lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3379_ = 1;
lean_inc(v_attrName_3320_);
v___x_3380_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3320_, v___x_3379_);
v___x_3381_ = lean_string_append(v___x_3378_, v___x_3380_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3383_ = lean_string_append(v___x_3381_, v___x_3382_);
v___y_3333_ = v___y_3377_;
v___y_3334_ = v___x_3383_;
goto v___jp_3332_;
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3320_);
v___x_3385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3320_, v_showInfo_3322_);
v___x_3386_ = lean_string_append(v___x_3384_, v___x_3385_);
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3388_ = lean_string_append(v___x_3386_, v___x_3387_);
v___x_3389_ = lean_string_append(v___x_3388_, v___x_3385_);
lean_dec_ref(v___x_3385_);
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3391_ = lean_string_append(v___x_3389_, v___x_3390_);
v___y_3333_ = v___y_3377_;
v___y_3334_ = v___x_3391_;
goto v___jp_3332_;
}
}
else
{
if (v_showInfo_3322_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3320_);
v___x_3393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3320_, v_minIndexable_3321_);
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
lean_dec_ref(v___x_3393_);
v___x_3395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3396_ = lean_string_append(v___x_3394_, v___x_3395_);
v___y_3333_ = v___y_3377_;
v___y_3334_ = v___x_3396_;
goto v___jp_3332_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3320_);
v___x_3398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3320_, v_showInfo_3322_);
v___x_3399_ = lean_string_append(v___x_3397_, v___x_3398_);
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3401_ = lean_string_append(v___x_3399_, v___x_3400_);
v___x_3402_ = lean_string_append(v___x_3401_, v___x_3398_);
lean_dec_ref(v___x_3398_);
v___x_3403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3404_ = lean_string_append(v___x_3402_, v___x_3403_);
v___y_3333_ = v___y_3377_;
v___y_3334_ = v___x_3404_;
goto v___jp_3332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3411_, lean_object* v_minIndexable_3412_, lean_object* v_showInfo_3413_, lean_object* v_ext_3414_, lean_object* v_ref_3415_, lean_object* v_a_3416_){
_start:
{
uint8_t v_minIndexable_boxed_3417_; uint8_t v_showInfo_boxed_3418_; lean_object* v_res_3419_; 
v_minIndexable_boxed_3417_ = lean_unbox(v_minIndexable_3412_);
v_showInfo_boxed_3418_ = lean_unbox(v_showInfo_3413_);
v_res_3419_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3411_, v_minIndexable_boxed_3417_, v_showInfo_boxed_3418_, v_ext_3414_, v_ref_3415_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3420_, lean_object* v_msg_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3428_, lean_object* v_msg_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3428_, v_msg_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3436_, uint8_t v_attrKind_3437_, uint8_t v_showInfo_3438_, uint8_t v_minIndexable_3439_, lean_object* v_as_3440_, lean_object* v_as_x27_3441_, lean_object* v_b_3442_, lean_object* v_a_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3436_, v_attrKind_3437_, v_showInfo_3438_, v_minIndexable_3439_, v_as_x27_3441_, v_b_3442_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3450_, lean_object* v_attrKind_3451_, lean_object* v_showInfo_3452_, lean_object* v_minIndexable_3453_, lean_object* v_as_3454_, lean_object* v_as_x27_3455_, lean_object* v_b_3456_, lean_object* v_a_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
uint8_t v_attrKind_boxed_3463_; uint8_t v_showInfo_boxed_3464_; uint8_t v_minIndexable_boxed_3465_; lean_object* v_res_3466_; 
v_attrKind_boxed_3463_ = lean_unbox(v_attrKind_3451_);
v_showInfo_boxed_3464_ = lean_unbox(v_showInfo_3452_);
v_minIndexable_boxed_3465_ = lean_unbox(v_minIndexable_3453_);
v_res_3466_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3450_, v_attrKind_boxed_3463_, v_showInfo_boxed_3464_, v_minIndexable_boxed_3465_, v_as_3454_, v_as_x27_3455_, v_b_3456_, v_a_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v_as_x27_3455_);
lean_dec(v_as_3454_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3467_, lean_object* v_x_3468_, uint8_t v_isExporting_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3468_, v_isExporting_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3476_, lean_object* v_x_3477_, lean_object* v_isExporting_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
uint8_t v_isExporting_boxed_3484_; lean_object* v_res_3485_; 
v_isExporting_boxed_3484_ = lean_unbox(v_isExporting_3478_);
v_res_3485_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3476_, v_x_3477_, v_isExporting_boxed_3484_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3486_, lean_object* v_x_3487_, uint8_t v_when_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3487_, v_when_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3495_, lean_object* v_x_3496_, lean_object* v_when_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
uint8_t v_when_boxed_3503_; lean_object* v_res_3504_; 
v_when_boxed_3503_ = lean_unbox(v_when_3497_);
v_res_3504_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3495_, v_x_3496_, v_when_boxed_3503_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3505_, lean_object* v_m_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3506_, v_a_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3509_, lean_object* v_m_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3509_, v_m_3510_, v_a_3511_);
lean_dec(v_a_3511_);
lean_dec_ref(v_m_3510_);
return v_res_3512_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3513_, lean_object* v_x_3514_, lean_object* v_x_3515_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3514_, v_x_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3517_, lean_object* v_x_3518_, lean_object* v_x_3519_){
_start:
{
uint8_t v_res_3520_; lean_object* v_r_3521_; 
v_res_3520_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3517_, v_x_3518_, v_x_3519_);
lean_dec_ref(v_x_3519_);
lean_dec_ref(v_x_3518_);
v_r_3521_ = lean_box(v_res_3520_);
return v_r_3521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3522_, lean_object* v_a_3523_, lean_object* v_x_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3523_, v_x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3526_, lean_object* v_a_3527_, lean_object* v_x_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3526_, v_a_3527_, v_x_3528_);
lean_dec(v_x_3528_);
lean_dec(v_a_3527_);
return v_res_3529_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3530_, lean_object* v_x_3531_, size_t v_x_3532_, lean_object* v_x_3533_){
_start:
{
uint8_t v___x_3534_; 
v___x_3534_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3531_, v_x_3532_, v_x_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3535_, lean_object* v_x_3536_, lean_object* v_x_3537_, lean_object* v_x_3538_){
_start:
{
size_t v_x_16922__boxed_3539_; uint8_t v_res_3540_; lean_object* v_r_3541_; 
v_x_16922__boxed_3539_ = lean_unbox_usize(v_x_3537_);
lean_dec(v_x_3537_);
v_res_3540_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3535_, v_x_3536_, v_x_16922__boxed_3539_, v_x_3538_);
lean_dec_ref(v_x_3538_);
lean_dec_ref(v_x_3536_);
v_r_3541_ = lean_box(v_res_3540_);
return v_r_3541_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3542_, lean_object* v_keys_3543_, lean_object* v_vals_3544_, lean_object* v_heq_3545_, lean_object* v_i_3546_, lean_object* v_k_3547_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3543_, v_i_3546_, v_k_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3549_, lean_object* v_keys_3550_, lean_object* v_vals_3551_, lean_object* v_heq_3552_, lean_object* v_i_3553_, lean_object* v_k_3554_){
_start:
{
uint8_t v_res_3555_; lean_object* v_r_3556_; 
v_res_3555_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3549_, v_keys_3550_, v_vals_3551_, v_heq_3552_, v_i_3553_, v_k_3554_);
lean_dec_ref(v_k_3554_);
lean_dec_ref(v_vals_3551_);
lean_dec_ref(v_keys_3550_);
v_r_3556_ = lean_box(v_res_3555_);
return v_r_3556_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_box(0);
v___x_3558_ = lean_unsigned_to_nat(16u);
v___x_3559_ = lean_mk_array(v___x_3558_, v___x_3557_);
return v___x_3559_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3561_ = lean_unsigned_to_nat(0u);
v___x_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
lean_ctor_set(v___x_3562_, 1, v___x_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3565_ = lean_st_mk_ref(v___x_3564_);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3569_, lean_object* v_msg_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_ref_3574_; lean_object* v___x_3575_; lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3621_; 
v_ref_3574_ = lean_ctor_get(v___y_3571_, 2);
v___x_3575_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3570_, v___y_3571_, v___y_3572_);
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3621_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3621_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v_traceState_3581_; lean_object* v_env_3582_; lean_object* v_nextMacroScope_3583_; lean_object* v_ngen_3584_; lean_object* v_auxDeclNGen_3585_; lean_object* v_cache_3586_; lean_object* v_recordedDeps_3587_; lean_object* v_messages_3588_; lean_object* v_infoState_3589_; lean_object* v_snapshotTasks_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3620_; 
v___x_3580_ = lean_st_ref_take(v___y_3572_);
v_traceState_3581_ = lean_ctor_get(v___x_3580_, 4);
v_env_3582_ = lean_ctor_get(v___x_3580_, 0);
v_nextMacroScope_3583_ = lean_ctor_get(v___x_3580_, 1);
v_ngen_3584_ = lean_ctor_get(v___x_3580_, 2);
v_auxDeclNGen_3585_ = lean_ctor_get(v___x_3580_, 3);
v_cache_3586_ = lean_ctor_get(v___x_3580_, 5);
v_recordedDeps_3587_ = lean_ctor_get(v___x_3580_, 6);
v_messages_3588_ = lean_ctor_get(v___x_3580_, 7);
v_infoState_3589_ = lean_ctor_get(v___x_3580_, 8);
v_snapshotTasks_3590_ = lean_ctor_get(v___x_3580_, 9);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3592_ = v___x_3580_;
v_isShared_3593_ = v_isSharedCheck_3620_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_snapshotTasks_3590_);
lean_inc(v_infoState_3589_);
lean_inc(v_messages_3588_);
lean_inc(v_recordedDeps_3587_);
lean_inc(v_cache_3586_);
lean_inc(v_traceState_3581_);
lean_inc(v_auxDeclNGen_3585_);
lean_inc(v_ngen_3584_);
lean_inc(v_nextMacroScope_3583_);
lean_inc(v_env_3582_);
lean_dec(v___x_3580_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3620_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
uint64_t v_tid_3594_; lean_object* v_traces_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3619_; 
v_tid_3594_ = lean_ctor_get_uint64(v_traceState_3581_, sizeof(void*)*1);
v_traces_3595_ = lean_ctor_get(v_traceState_3581_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_traceState_3581_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3597_ = v_traceState_3581_;
v_isShared_3598_ = v_isSharedCheck_3619_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_traces_3595_);
lean_dec(v_traceState_3581_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3619_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; double v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3599_ = lean_box(0);
v___x_3600_ = lean_box(0);
v___x_3601_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3602_ = 0;
v___x_3603_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3604_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3604_, 0, v_cls_3569_);
lean_ctor_set(v___x_3604_, 1, v___x_3600_);
lean_ctor_set(v___x_3604_, 2, v___x_3603_);
lean_ctor_set_float(v___x_3604_, sizeof(void*)*3, v___x_3601_);
lean_ctor_set_float(v___x_3604_, sizeof(void*)*3 + 8, v___x_3601_);
lean_ctor_set_uint8(v___x_3604_, sizeof(void*)*3 + 16, v___x_3602_);
v___x_3605_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3606_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v_a_3576_);
lean_ctor_set(v___x_3606_, 2, v___x_3605_);
lean_inc(v_ref_3574_);
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v_ref_3574_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Lean_PersistentArray_push___redArg(v_traces_3595_, v___x_3607_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3608_);
v___x_3610_ = v___x_3597_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3608_);
lean_ctor_set_uint64(v_reuseFailAlloc_3618_, sizeof(void*)*1, v_tid_3594_);
v___x_3610_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 4, v___x_3610_);
v___x_3612_ = v___x_3592_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_env_3582_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_nextMacroScope_3583_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_ngen_3584_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_auxDeclNGen_3585_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3617_, 5, v_cache_3586_);
lean_ctor_set(v_reuseFailAlloc_3617_, 6, v_recordedDeps_3587_);
lean_ctor_set(v_reuseFailAlloc_3617_, 7, v_messages_3588_);
lean_ctor_set(v_reuseFailAlloc_3617_, 8, v_infoState_3589_);
lean_ctor_set(v_reuseFailAlloc_3617_, 9, v_snapshotTasks_3590_);
v___x_3612_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3613_ = lean_st_ref_put(v___y_3572_, v___x_3612_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3599_);
v___x_3615_ = v___x_3578_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3599_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3622_, lean_object* v_msg_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3622_, v_msg_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3628_, uint8_t v_isMeta_3629_, lean_object* v_hint_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v_env_3636_; uint8_t v_isExporting_3637_; lean_object* v_entry_3638_; lean_object* v___x_3639_; lean_object* v_env_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___y_3645_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3634_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_3635_ = lean_st_ref_get(v___y_3632_);
v_env_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc_ref(v_env_3636_);
lean_dec(v___x_3635_);
v_isExporting_3637_ = lean_ctor_get_uint8(v_env_3636_, sizeof(void*)*8);
lean_dec_ref(v_env_3636_);
lean_inc(v_mod_3628_);
v_entry_3638_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3638_, 0, v_mod_3628_);
lean_ctor_set_uint8(v_entry_3638_, sizeof(void*)*1, v_isExporting_3637_);
lean_ctor_set_uint8(v_entry_3638_, sizeof(void*)*1 + 1, v_isMeta_3629_);
v___x_3639_ = lean_st_ref_get(v___y_3632_);
v_env_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc_ref(v_env_3640_);
lean_dec(v___x_3639_);
v___x_3641_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3642_ = lean_box(1);
v___x_3643_ = lean_box(0);
v___x_3671_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3634_, v___x_3641_, v_env_3640_, v___x_3642_, v___x_3643_);
v___x_3672_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3671_, v_entry_3638_);
lean_dec(v___x_3671_);
if (v___x_3672_ == 0)
{
lean_object* v_toCold_3673_; lean_object* v_options_3674_; uint8_t v_hasTrace_3675_; 
v_toCold_3673_ = lean_ctor_get(v___y_3631_, 0);
v_options_3674_ = lean_ctor_get(v_toCold_3673_, 2);
v_hasTrace_3675_ = lean_ctor_get_uint8(v_options_3674_, sizeof(void*)*1);
if (v_hasTrace_3675_ == 0)
{
lean_dec(v_hint_3630_);
lean_dec(v_mod_3628_);
v___y_3645_ = v___y_3632_;
goto v___jp_3644_;
}
else
{
lean_object* v_inheritedTraceOptions_3676_; lean_object* v_cls_3677_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___x_3697_; uint8_t v___x_3698_; 
v_inheritedTraceOptions_3676_ = lean_ctor_get(v_toCold_3673_, 11);
v_cls_3677_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_3697_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_3698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3676_, v_options_3674_, v___x_3697_);
if (v___x_3698_ == 0)
{
lean_dec(v_hint_3630_);
lean_dec(v_mod_3628_);
v___y_3645_ = v___y_3632_;
goto v___jp_3644_;
}
else
{
lean_object* v___x_3699_; lean_object* v___y_3701_; 
v___x_3699_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_3637_ == 0)
{
lean_object* v___x_3708_; 
v___x_3708_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3701_ = v___x_3708_;
goto v___jp_3700_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3701_ = v___x_3709_;
goto v___jp_3700_;
}
v___jp_3700_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_inc_ref(v___y_3701_);
v___x_3702_ = l_Lean_stringToMessageData(v___y_3701_);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3699_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
if (v_isMeta_3629_ == 0)
{
lean_object* v___x_3706_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_3684_ = v___x_3705_;
v___y_3685_ = v___x_3706_;
goto v___jp_3683_;
}
else
{
lean_object* v___x_3707_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_3684_ = v___x_3705_;
v___y_3685_ = v___x_3707_;
goto v___jp_3683_;
}
}
}
v___jp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___y_3679_);
lean_ctor_set(v___x_3681_, 1, v___y_3680_);
v___x_3682_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3677_, v___x_3681_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_dec_ref_known(v___x_3682_, 1);
v___y_3645_ = v___y_3632_;
goto v___jp_3644_;
}
else
{
lean_dec_ref_known(v_entry_3638_, 1);
return v___x_3682_;
}
}
v___jp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
lean_inc_ref(v___y_3685_);
v___x_3686_ = l_Lean_stringToMessageData(v___y_3685_);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___y_3684_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_3689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = l_Lean_MessageData_ofName(v_mod_3628_);
v___x_3691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3689_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = l_Lean_Name_isAnonymous(v_hint_3630_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3694_ = l_Lean_MessageData_ofName(v_hint_3630_);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___y_3679_ = v___x_3691_;
v___y_3680_ = v___x_3695_;
goto v___jp_3678_;
}
else
{
lean_object* v___x_3696_; 
lean_dec(v_hint_3630_);
v___x_3696_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_3679_ = v___x_3691_;
v___y_3680_ = v___x_3696_;
goto v___jp_3678_;
}
}
}
}
else
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
lean_dec_ref_known(v_entry_3638_, 1);
lean_dec(v_hint_3630_);
lean_dec(v_mod_3628_);
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
v___jp_3644_:
{
lean_object* v___x_3646_; lean_object* v_toEnvExtension_3647_; lean_object* v_env_3648_; lean_object* v_nextMacroScope_3649_; lean_object* v_ngen_3650_; lean_object* v_auxDeclNGen_3651_; lean_object* v_traceState_3652_; lean_object* v_recordedDeps_3653_; lean_object* v_messages_3654_; lean_object* v_infoState_3655_; lean_object* v_snapshotTasks_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3669_; 
v___x_3646_ = lean_st_ref_take(v___y_3645_);
v_toEnvExtension_3647_ = lean_ctor_get(v___x_3641_, 0);
v_env_3648_ = lean_ctor_get(v___x_3646_, 0);
v_nextMacroScope_3649_ = lean_ctor_get(v___x_3646_, 1);
v_ngen_3650_ = lean_ctor_get(v___x_3646_, 2);
v_auxDeclNGen_3651_ = lean_ctor_get(v___x_3646_, 3);
v_traceState_3652_ = lean_ctor_get(v___x_3646_, 4);
v_recordedDeps_3653_ = lean_ctor_get(v___x_3646_, 6);
v_messages_3654_ = lean_ctor_get(v___x_3646_, 7);
v_infoState_3655_ = lean_ctor_get(v___x_3646_, 8);
v_snapshotTasks_3656_ = lean_ctor_get(v___x_3646_, 9);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; 
v_unused_3670_ = lean_ctor_get(v___x_3646_, 5);
lean_dec(v_unused_3670_);
v___x_3658_ = v___x_3646_;
v_isShared_3659_ = v_isSharedCheck_3669_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_snapshotTasks_3656_);
lean_inc(v_infoState_3655_);
lean_inc(v_messages_3654_);
lean_inc(v_recordedDeps_3653_);
lean_inc(v_traceState_3652_);
lean_inc(v_auxDeclNGen_3651_);
lean_inc(v_ngen_3650_);
lean_inc(v_nextMacroScope_3649_);
lean_inc(v_env_3648_);
lean_dec(v___x_3646_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3669_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v_asyncMode_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v_asyncMode_3660_ = lean_ctor_get(v_toEnvExtension_3647_, 2);
v___x_3661_ = lean_box(0);
v___x_3662_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3641_, v_env_3648_, v_entry_3638_, v_asyncMode_3660_, v___x_3643_);
v___x_3663_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 5, v___x_3663_);
lean_ctor_set(v___x_3658_, 0, v___x_3662_);
v___x_3665_ = v___x_3658_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_nextMacroScope_3649_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_ngen_3650_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_auxDeclNGen_3651_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_traceState_3652_);
lean_ctor_set(v_reuseFailAlloc_3668_, 5, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3668_, 6, v_recordedDeps_3653_);
lean_ctor_set(v_reuseFailAlloc_3668_, 7, v_messages_3654_);
lean_ctor_set(v_reuseFailAlloc_3668_, 8, v_infoState_3655_);
lean_ctor_set(v_reuseFailAlloc_3668_, 9, v_snapshotTasks_3656_);
v___x_3665_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_st_ref_put(v___y_3645_, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3661_);
return v___x_3667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3712_, lean_object* v_isMeta_3713_, lean_object* v_hint_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
uint8_t v_isMeta_boxed_3718_; lean_object* v_res_3719_; 
v_isMeta_boxed_3718_ = lean_unbox(v_isMeta_3713_);
v_res_3719_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3712_, v_isMeta_boxed_3718_, v_hint_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3720_, lean_object* v_declName_3721_, lean_object* v_as_3722_, size_t v_sz_3723_, size_t v_i_3724_, lean_object* v_b_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v___x_3729_; 
v___x_3729_ = lean_usize_dec_lt(v_i_3724_, v_sz_3723_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; 
lean_dec(v_declName_3721_);
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v_b_3725_);
return v___x_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v_modules_3732_; lean_object* v___x_3733_; lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v_toImport_3736_; lean_object* v_module_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; lean_object* v___x_3740_; 
v___x_3731_ = l_Lean_Environment_header(v___x_3720_);
v_modules_3732_ = lean_ctor_get(v___x_3731_, 3);
lean_inc_ref(v_modules_3732_);
lean_dec_ref(v___x_3731_);
v___x_3733_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3734_ = lean_array_uget_borrowed(v_as_3722_, v_i_3724_);
v___x_3735_ = lean_array_get(v___x_3733_, v_modules_3732_, v_a_3734_);
lean_dec_ref(v_modules_3732_);
v_toImport_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc_ref(v_toImport_3736_);
lean_dec(v___x_3735_);
v_module_3737_ = lean_ctor_get(v_toImport_3736_, 0);
lean_inc(v_module_3737_);
lean_dec_ref(v_toImport_3736_);
v___x_3738_ = lean_box(0);
v___x_3739_ = 0;
lean_inc(v_declName_3721_);
v___x_3740_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3737_, v___x_3739_, v_declName_3721_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3740_) == 0)
{
size_t v___x_3741_; size_t v___x_3742_; 
lean_dec_ref_known(v___x_3740_, 1);
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = lean_usize_add(v_i_3724_, v___x_3741_);
v_i_3724_ = v___x_3742_;
v_b_3725_ = v___x_3738_;
goto _start;
}
else
{
lean_dec(v_declName_3721_);
return v___x_3740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3744_, lean_object* v_declName_3745_, lean_object* v_as_3746_, lean_object* v_sz_3747_, lean_object* v_i_3748_, lean_object* v_b_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
size_t v_sz_boxed_3753_; size_t v_i_boxed_3754_; lean_object* v_res_3755_; 
v_sz_boxed_3753_ = lean_unbox_usize(v_sz_3747_);
lean_dec(v_sz_3747_);
v_i_boxed_3754_ = lean_unbox_usize(v_i_3748_);
lean_dec(v_i_3748_);
v_res_3755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3744_, v_declName_3745_, v_as_3746_, v_sz_boxed_3753_, v_i_boxed_3754_, v_b_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec_ref(v_as_3746_);
lean_dec_ref(v___x_3744_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3756_, uint8_t v_isMeta_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_env_3766_; lean_object* v___y_3768_; lean_object* v___x_3781_; 
v___x_3761_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3762_ = lean_st_ref_get(v___y_3759_);
v_env_3766_ = lean_ctor_get(v___x_3762_, 0);
lean_inc_ref(v_env_3766_);
lean_dec(v___x_3762_);
v___x_3781_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3766_, v_declName_3756_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_dec_ref(v_env_3766_);
lean_dec(v_declName_3756_);
goto v___jp_3763_;
}
else
{
lean_object* v_val_3782_; lean_object* v___x_3783_; lean_object* v_modules_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; 
v_val_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_val_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v___x_3783_ = l_Lean_Environment_header(v_env_3766_);
v_modules_3784_ = lean_ctor_get(v___x_3783_, 3);
lean_inc_ref(v_modules_3784_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = lean_array_get_size(v_modules_3784_);
v___x_3786_ = lean_nat_dec_lt(v_val_3782_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_dec_ref(v_modules_3784_);
lean_dec(v_val_3782_);
lean_dec_ref(v_env_3766_);
lean_dec(v_declName_3756_);
goto v___jp_3763_;
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___y_3790_; 
v___x_3787_ = lean_array_fget(v_modules_3784_, v_val_3782_);
lean_dec(v_val_3782_);
lean_dec_ref(v_modules_3784_);
v___x_3788_ = lean_st_ref_get(v___y_3759_);
if (v_isMeta_3757_ == 0)
{
lean_dec(v___x_3788_);
v___y_3790_ = v_isMeta_3757_;
goto v___jp_3789_;
}
else
{
lean_object* v_env_3801_; uint8_t v___x_3802_; 
v_env_3801_ = lean_ctor_get(v___x_3788_, 0);
lean_inc_ref(v_env_3801_);
lean_dec(v___x_3788_);
lean_inc(v_declName_3756_);
v___x_3802_ = l_Lean_isMarkedMeta(v_env_3801_, v_declName_3756_);
if (v___x_3802_ == 0)
{
v___y_3790_ = v_isMeta_3757_;
goto v___jp_3789_;
}
else
{
uint8_t v___x_3803_; 
v___x_3803_ = 0;
v___y_3790_ = v___x_3803_;
goto v___jp_3789_;
}
}
v___jp_3789_:
{
lean_object* v_toImport_3791_; lean_object* v_module_3792_; lean_object* v___x_3793_; 
v_toImport_3791_ = lean_ctor_get(v___x_3787_, 0);
lean_inc_ref(v_toImport_3791_);
lean_dec(v___x_3787_);
v_module_3792_ = lean_ctor_get(v_toImport_3791_, 0);
lean_inc(v_module_3792_);
lean_dec_ref(v_toImport_3791_);
lean_inc(v_declName_3756_);
v___x_3793_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3792_, v___y_3790_, v_declName_3756_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_dec_ref_known(v___x_3793_, 1);
v___x_3794_ = l_Lean_indirectModUseExt;
v___x_3795_ = lean_box(1);
v___x_3796_ = lean_box(0);
lean_inc_ref(v_env_3766_);
v___x_3797_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3761_, v___x_3794_, v_env_3766_, v___x_3795_, v___x_3796_);
v___x_3798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3797_, v_declName_3756_);
lean_dec(v___x_3797_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v___x_3799_; 
v___x_3799_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3768_ = v___x_3799_;
goto v___jp_3767_;
}
else
{
lean_object* v_val_3800_; 
v_val_3800_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_val_3800_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3768_ = v_val_3800_;
goto v___jp_3767_;
}
}
else
{
lean_dec_ref(v_env_3766_);
lean_dec(v_declName_3756_);
return v___x_3793_;
}
}
}
}
v___jp_3763_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_box(0);
v___x_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
return v___x_3765_;
}
v___jp_3767_:
{
lean_object* v___x_3769_; size_t v_sz_3770_; size_t v___x_3771_; lean_object* v___x_3772_; 
v___x_3769_ = lean_box(0);
v_sz_3770_ = lean_array_size(v___y_3768_);
v___x_3771_ = ((size_t)0ULL);
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3766_, v_declName_3756_, v___y_3768_, v_sz_3770_, v___x_3771_, v___x_3769_, v___y_3758_, v___y_3759_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v_env_3766_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v___x_3772_, 0);
lean_dec(v_unused_3780_);
v___x_3774_ = v___x_3772_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_dec(v___x_3772_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v___x_3769_);
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3769_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
else
{
return v___x_3772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3804_, lean_object* v_isMeta_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
uint8_t v_isMeta_boxed_3809_; lean_object* v_res_3810_; 
v_isMeta_boxed_3809_ = lean_unbox(v_isMeta_3805_);
v_res_3810_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3804_, v_isMeta_boxed_3809_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3815_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3816_ = lean_st_ref_get(v___x_3815_);
v___x_3817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3816_, v_attrName_3811_);
lean_dec(v___x_3816_);
if (lean_obj_tag(v___x_3817_) == 1)
{
lean_object* v_val_3818_; lean_object* v_ext_3819_; lean_object* v_name_3820_; uint8_t v___x_3821_; lean_object* v___x_3822_; 
v_val_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_val_3818_);
v_ext_3819_ = lean_ctor_get(v_val_3818_, 1);
lean_inc_ref(v_ext_3819_);
lean_dec(v_val_3818_);
v_name_3820_ = lean_ctor_get(v_ext_3819_, 1);
lean_inc(v_name_3820_);
lean_dec_ref(v_ext_3819_);
v___x_3821_ = 1;
v___x_3822_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3820_, v___x_3821_, v_a_3812_, v_a_3813_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3829_ == 0)
{
lean_object* v_unused_3830_; 
v_unused_3830_ = lean_ctor_get(v___x_3822_, 0);
lean_dec(v_unused_3830_);
v___x_3824_ = v___x_3822_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_dec(v___x_3822_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3817_);
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3817_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref_known(v___x_3817_, 1);
v_a_3831_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3822_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3822_);
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
}
else
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3817_);
return v___x_3839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3840_, v_a_3841_, v_a_3842_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_attrName_3840_);
return v_res_3844_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3846_, lean_object* v_x_3847_){
_start:
{
if (lean_obj_tag(v_x_3847_) == 0)
{
return v_x_3846_;
}
else
{
lean_object* v_key_3848_; lean_object* v_value_3849_; lean_object* v_tail_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3876_; 
v_key_3848_ = lean_ctor_get(v_x_3847_, 0);
v_value_3849_ = lean_ctor_get(v_x_3847_, 1);
v_tail_3850_ = lean_ctor_get(v_x_3847_, 2);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_x_3847_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3852_ = v_x_3847_;
v_isShared_3853_ = v_isSharedCheck_3876_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_tail_3850_);
lean_inc(v_value_3849_);
lean_inc(v_key_3848_);
lean_dec(v_x_3847_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3876_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; uint64_t v___y_3856_; 
v___x_3854_ = lean_array_get_size(v_x_3846_);
if (lean_obj_tag(v_key_3848_) == 0)
{
uint64_t v___x_3874_; 
v___x_3874_ = 1723ULL;
v___y_3856_ = v___x_3874_;
goto v___jp_3855_;
}
else
{
uint64_t v_hash_3875_; 
v_hash_3875_ = lean_ctor_get_uint64(v_key_3848_, sizeof(void*)*2);
v___y_3856_ = v_hash_3875_;
goto v___jp_3855_;
}
v___jp_3855_:
{
uint64_t v___x_3857_; uint64_t v___x_3858_; uint64_t v_fold_3859_; uint64_t v___x_3860_; uint64_t v___x_3861_; uint64_t v___x_3862_; size_t v___x_3863_; size_t v___x_3864_; size_t v___x_3865_; size_t v___x_3866_; size_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3857_ = 32ULL;
v___x_3858_ = lean_uint64_shift_right(v___y_3856_, v___x_3857_);
v_fold_3859_ = lean_uint64_xor(v___y_3856_, v___x_3858_);
v___x_3860_ = 16ULL;
v___x_3861_ = lean_uint64_shift_right(v_fold_3859_, v___x_3860_);
v___x_3862_ = lean_uint64_xor(v_fold_3859_, v___x_3861_);
v___x_3863_ = lean_uint64_to_usize(v___x_3862_);
v___x_3864_ = lean_usize_of_nat(v___x_3854_);
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_sub(v___x_3864_, v___x_3865_);
v___x_3867_ = lean_usize_land(v___x_3863_, v___x_3866_);
v___x_3868_ = lean_array_uget_borrowed(v_x_3846_, v___x_3867_);
lean_inc(v___x_3868_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 2, v___x_3868_);
v___x_3870_ = v___x_3852_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_key_3848_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_value_3849_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_array_uset(v_x_3846_, v___x_3867_, v___x_3870_);
v_x_3846_ = v___x_3871_;
v_x_3847_ = v_tail_3850_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3877_, lean_object* v_source_3878_, lean_object* v_target_3879_){
_start:
{
lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3880_ = lean_array_get_size(v_source_3878_);
v___x_3881_ = lean_nat_dec_lt(v_i_3877_, v___x_3880_);
if (v___x_3881_ == 0)
{
lean_dec_ref(v_source_3878_);
lean_dec(v_i_3877_);
return v_target_3879_;
}
else
{
lean_object* v_es_3882_; lean_object* v___x_3883_; lean_object* v_source_3884_; lean_object* v_target_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_es_3882_ = lean_array_fget(v_source_3878_, v_i_3877_);
v___x_3883_ = lean_box(0);
v_source_3884_ = lean_array_fset(v_source_3878_, v_i_3877_, v___x_3883_);
v_target_3885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3879_, v_es_3882_);
v___x_3886_ = lean_unsigned_to_nat(1u);
v___x_3887_ = lean_nat_add(v_i_3877_, v___x_3886_);
lean_dec(v_i_3877_);
v_i_3877_ = v___x_3887_;
v_source_3878_ = v_source_3884_;
v_target_3879_ = v_target_3885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3889_){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v_nbuckets_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3890_ = lean_array_get_size(v_data_3889_);
v___x_3891_ = lean_unsigned_to_nat(2u);
v_nbuckets_3892_ = lean_nat_mul(v___x_3890_, v___x_3891_);
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = lean_box(0);
v___x_3895_ = lean_mk_array(v_nbuckets_3892_, v___x_3894_);
v___x_3896_ = lean_array_propagate_mark(v_data_3889_, v___x_3895_);
v___x_3897_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3893_, v_data_3889_, v___x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3898_, lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3899_) == 0)
{
uint8_t v___x_3900_; 
v___x_3900_ = 0;
return v___x_3900_;
}
else
{
lean_object* v_key_3901_; lean_object* v_tail_3902_; uint8_t v___x_3903_; 
v_key_3901_ = lean_ctor_get(v_x_3899_, 0);
v_tail_3902_ = lean_ctor_get(v_x_3899_, 2);
v___x_3903_ = lean_name_eq(v_key_3901_, v_a_3898_);
if (v___x_3903_ == 0)
{
v_x_3899_ = v_tail_3902_;
goto _start;
}
else
{
return v___x_3903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3905_, lean_object* v_x_3906_){
_start:
{
uint8_t v_res_3907_; lean_object* v_r_3908_; 
v_res_3907_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3905_, v_x_3906_);
lean_dec(v_x_3906_);
lean_dec(v_a_3905_);
v_r_3908_ = lean_box(v_res_3907_);
return v_r_3908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3909_, lean_object* v_b_3910_, lean_object* v_x_3911_){
_start:
{
if (lean_obj_tag(v_x_3911_) == 0)
{
lean_dec(v_b_3910_);
lean_dec(v_a_3909_);
return v_x_3911_;
}
else
{
lean_object* v_key_3912_; lean_object* v_value_3913_; lean_object* v_tail_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3926_; 
v_key_3912_ = lean_ctor_get(v_x_3911_, 0);
v_value_3913_ = lean_ctor_get(v_x_3911_, 1);
v_tail_3914_ = lean_ctor_get(v_x_3911_, 2);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_x_3911_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3916_ = v_x_3911_;
v_isShared_3917_ = v_isSharedCheck_3926_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_tail_3914_);
lean_inc(v_value_3913_);
lean_inc(v_key_3912_);
lean_dec(v_x_3911_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3926_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
uint8_t v___x_3918_; 
v___x_3918_ = lean_name_eq(v_key_3912_, v_a_3909_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3919_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3909_, v_b_3910_, v_tail_3914_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 2, v___x_3919_);
v___x_3921_ = v___x_3916_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_key_3912_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_value_3913_);
lean_ctor_set(v_reuseFailAlloc_3922_, 2, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
else
{
lean_object* v___x_3924_; 
lean_dec(v_value_3913_);
lean_dec(v_key_3912_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 1, v_b_3910_);
lean_ctor_set(v___x_3916_, 0, v_a_3909_);
v___x_3924_ = v___x_3916_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3909_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_b_3910_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_tail_3914_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3927_, lean_object* v_a_3928_, lean_object* v_b_3929_){
_start:
{
lean_object* v_size_3930_; lean_object* v_buckets_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3977_; 
v_size_3930_ = lean_ctor_get(v_m_3927_, 0);
v_buckets_3931_ = lean_ctor_get(v_m_3927_, 1);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_m_3927_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3933_ = v_m_3927_;
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_buckets_3931_);
lean_inc(v_size_3930_);
lean_dec(v_m_3927_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; uint64_t v___y_3937_; 
v___x_3935_ = lean_array_get_size(v_buckets_3931_);
if (lean_obj_tag(v_a_3928_) == 0)
{
uint64_t v___x_3975_; 
v___x_3975_ = 1723ULL;
v___y_3937_ = v___x_3975_;
goto v___jp_3936_;
}
else
{
uint64_t v_hash_3976_; 
v_hash_3976_ = lean_ctor_get_uint64(v_a_3928_, sizeof(void*)*2);
v___y_3937_ = v_hash_3976_;
goto v___jp_3936_;
}
v___jp_3936_:
{
uint64_t v___x_3938_; uint64_t v___x_3939_; uint64_t v_fold_3940_; uint64_t v___x_3941_; uint64_t v___x_3942_; uint64_t v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; size_t v___x_3946_; size_t v___x_3947_; size_t v___x_3948_; lean_object* v_bkt_3949_; uint8_t v___x_3950_; 
v___x_3938_ = 32ULL;
v___x_3939_ = lean_uint64_shift_right(v___y_3937_, v___x_3938_);
v_fold_3940_ = lean_uint64_xor(v___y_3937_, v___x_3939_);
v___x_3941_ = 16ULL;
v___x_3942_ = lean_uint64_shift_right(v_fold_3940_, v___x_3941_);
v___x_3943_ = lean_uint64_xor(v_fold_3940_, v___x_3942_);
v___x_3944_ = lean_uint64_to_usize(v___x_3943_);
v___x_3945_ = lean_usize_of_nat(v___x_3935_);
v___x_3946_ = ((size_t)1ULL);
v___x_3947_ = lean_usize_sub(v___x_3945_, v___x_3946_);
v___x_3948_ = lean_usize_land(v___x_3944_, v___x_3947_);
v_bkt_3949_ = lean_array_uget_borrowed(v_buckets_3931_, v___x_3948_);
v___x_3950_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3928_, v_bkt_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; lean_object* v_size_x27_3952_; lean_object* v___x_3953_; lean_object* v_buckets_x27_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3951_ = lean_unsigned_to_nat(1u);
v_size_x27_3952_ = lean_nat_add(v_size_3930_, v___x_3951_);
lean_dec(v_size_3930_);
lean_inc(v_bkt_3949_);
v___x_3953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3953_, 0, v_a_3928_);
lean_ctor_set(v___x_3953_, 1, v_b_3929_);
lean_ctor_set(v___x_3953_, 2, v_bkt_3949_);
v_buckets_x27_3954_ = lean_array_uset(v_buckets_3931_, v___x_3948_, v___x_3953_);
v___x_3955_ = lean_unsigned_to_nat(4u);
v___x_3956_ = lean_nat_mul(v_size_x27_3952_, v___x_3955_);
v___x_3957_ = lean_unsigned_to_nat(3u);
v___x_3958_ = lean_nat_div(v___x_3956_, v___x_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_array_get_size(v_buckets_x27_3954_);
v___x_3960_ = lean_nat_dec_le(v___x_3958_, v___x_3959_);
lean_dec(v___x_3958_);
if (v___x_3960_ == 0)
{
lean_object* v_val_3961_; lean_object* v___x_3963_; 
v_val_3961_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3954_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_val_3961_);
lean_ctor_set(v___x_3933_, 0, v_size_x27_3952_);
v___x_3963_ = v___x_3933_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_size_x27_3952_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_val_3961_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
else
{
lean_object* v___x_3966_; 
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_buckets_x27_3954_);
lean_ctor_set(v___x_3933_, 0, v_size_x27_3952_);
v___x_3966_ = v___x_3933_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_size_x27_3952_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_buckets_x27_3954_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
else
{
lean_object* v___x_3968_; lean_object* v_buckets_x27_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
lean_inc(v_bkt_3949_);
v___x_3968_ = lean_box(0);
v_buckets_x27_3969_ = lean_array_uset(v_buckets_3931_, v___x_3948_, v___x_3968_);
v___x_3970_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3928_, v_b_3929_, v_bkt_3949_);
v___x_3971_ = lean_array_uset(v_buckets_x27_3969_, v___x_3948_, v___x_3970_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v___x_3971_);
v___x_3973_ = v___x_3933_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_size_3930_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3978_, lean_object* v_ref_3979_){
_start:
{
lean_object* v___x_3981_; 
lean_inc(v_ref_3979_);
v___x_3981_ = l_Lean_Meta_Grind_mkExtension(v_ref_3979_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; uint8_t v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc_n(v_a_3982_, 2);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = 0;
v___x_3984_ = 1;
lean_inc(v_ref_3979_);
lean_inc(v_attrName_3978_);
v___x_3985_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3983_, v___x_3984_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref_known(v___x_3985_, 1);
lean_inc(v_ref_3979_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3986_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3983_, v___x_3983_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref_known(v___x_3986_, 1);
lean_inc(v_ref_3979_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3987_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3984_, v___x_3984_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3988_; 
lean_dec_ref_known(v___x_3987_, 1);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3988_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3984_, v___x_3983_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3999_; 
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v___x_3988_, 0);
lean_dec(v_unused_4000_);
v___x_3990_ = v___x_3988_;
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v___x_3988_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3992_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3993_ = lean_st_ref_take(v___x_3992_);
lean_inc(v_a_3982_);
v___x_3994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_3993_, v_attrName_3978_, v_a_3982_);
v___x_3995_ = lean_st_ref_put(v___x_3992_, v___x_3994_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v_a_3982_);
v___x_3997_ = v___x_3990_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3982_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec(v_a_3982_);
lean_dec(v_attrName_3978_);
v_a_4001_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3988_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3988_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4009_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3987_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3987_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4017_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_3986_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_3986_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4025_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_3985_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_3985_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
return v___x_3981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4033_, lean_object* v_ref_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4033_, v_ref_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4037_, lean_object* v_m_4038_, lean_object* v_a_4039_, lean_object* v_b_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4038_, v_a_4039_, v_b_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4042_, lean_object* v_a_4043_, lean_object* v_x_4044_){
_start:
{
uint8_t v___x_4045_; 
v___x_4045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4043_, v_x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_a_4047_, lean_object* v_x_4048_){
_start:
{
uint8_t v_res_4049_; lean_object* v_r_4050_; 
v_res_4049_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4046_, v_a_4047_, v_x_4048_);
lean_dec(v_x_4048_);
lean_dec(v_a_4047_);
v_r_4050_ = lean_box(v_res_4049_);
return v_r_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4051_, lean_object* v_data_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4054_, lean_object* v_a_4055_, lean_object* v_b_4056_, lean_object* v_x_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4055_, v_b_4056_, v_x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4059_, lean_object* v_i_4060_, lean_object* v_source_4061_, lean_object* v_target_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4060_, v_source_4061_, v_target_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4064_, lean_object* v_x_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4065_, v_x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4076_ = l_Lean_Meta_Grind_registerAttr(v___x_4074_, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4091_ = l_Lean_Meta_Grind_registerAttr(v___x_4089_, v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v_env_4099_; lean_object* v___x_4100_; lean_object* v_ext_4101_; lean_object* v_toEnvExtension_4102_; lean_object* v_asyncMode_4103_; lean_object* v___x_4104_; lean_object* v_casesTypes_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4097_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4098_ = lean_st_ref_get(v_a_4095_);
v_env_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc_ref(v_env_4099_);
lean_dec(v___x_4098_);
v___x_4100_ = l_Lean_Meta_Grind_grindExt;
v_ext_4101_ = lean_ctor_get(v___x_4100_, 1);
v_toEnvExtension_4102_ = lean_ctor_get(v_ext_4101_, 0);
v_asyncMode_4103_ = lean_ctor_get(v_toEnvExtension_4102_, 2);
v___x_4104_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4097_, v___x_4100_, v_env_4099_, v_asyncMode_4103_);
v_casesTypes_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc_ref(v_casesTypes_4105_);
lean_dec(v___x_4104_);
v___x_4106_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4105_, v_declName_4094_);
lean_dec_ref(v_casesTypes_4105_);
v___x_4107_ = lean_box(v___x_4106_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4109_, v_a_4110_);
lean_dec(v_a_4110_);
lean_dec(v_declName_4109_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4113_, v_a_4115_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4118_, v_a_4119_, v_a_4120_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
lean_dec(v_declName_4118_);
return v_res_4122_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
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
