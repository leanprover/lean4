// Lean compiler output
// Module: Lake.Config.Artifact
// Imports: public import Lake.Build.Trace
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
lean_object* lean_nat_to_int(lean_object*);
extern uint64_t l_Lake_Hash_nil;
lean_object* l_Lake_instReprHash_repr___redArg(uint64_t);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofHex_x3f(lean_object*);
lean_object* l_Lake_Hash_hex(uint64_t);
static const lean_string_object l_Lake_artifactPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_artifactPath___closed__0 = (const lean_object*)&l_Lake_artifactPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_artifactPath(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_artifactPath___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedArtifactDescr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l_Lake_instInhabitedArtifactDescr_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedArtifactDescr_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedArtifactDescr_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifactDescr_default___closed__1;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifactDescr_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifactDescr;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprArtifactDescr_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hash"};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__12;
static const lean_string_object l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__14;
static lean_once_cell_t l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__15;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__16 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lake_instReprArtifactDescr_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__13_value)}};
static const lean_object* l_Lake_instReprArtifactDescr_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprArtifactDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprArtifactDescr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprArtifactDescr___closed__0 = (const lean_object*)&l_Lake_instReprArtifactDescr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprArtifactDescr = (const lean_object*)&l_Lake_instReprArtifactDescr___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_artifactWithExt(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_artifactWithExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_ArtifactDescr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ArtifactDescr_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ArtifactDescr_instToString___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ArtifactDescr_instToString = (const lean_object*)&l_Lake_ArtifactDescr_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_ArtifactDescr_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ArtifactDescr_instToJson___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ArtifactDescr_instToJson___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ArtifactDescr_instToJson = (const lean_object*)&l_Lake_ArtifactDescr_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "expected artifact file name to be a content hash"};
static const lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value;
static const lean_ctor_object l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__0_value)}};
static const lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1 = (const lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1_value;
static const lean_string_object l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2 = (const lean_object*)&l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ArtifactDescr_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "artifact in unexpected JSON format: "};
static const lean_object* l_Lake_ArtifactDescr_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_fromJson_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_ArtifactDescr_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ArtifactDescr_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ArtifactDescr_instFromJson___closed__0 = (const lean_object*)&l_Lake_ArtifactDescr_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ArtifactDescr_instFromJson = (const lean_object*)&l_Lake_ArtifactDescr_instFromJson___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedArtifact_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifact_default___closed__0;
static lean_once_cell_t l_Lake_instInhabitedArtifact_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifact_default___closed__1;
static lean_once_cell_t l_Lake_instInhabitedArtifact_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedArtifact_default___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifact_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedArtifact;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "descr"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprArtifactDescr_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprArtifact_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprArtifact_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__6_value;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__7 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__7_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__8_value;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__9_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__10_value;
static const lean_string_object l_Lake_instReprArtifact_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mtime"};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lake_instReprArtifact_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__11_value)}};
static const lean_object* l_Lake_instReprArtifact_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprArtifact_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprArtifact_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprArtifact___closed__0 = (const lean_object*)&l_Lake_instReprArtifact___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprArtifact = (const lean_object*)&l_Lake_instReprArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Artifact_withName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Artifact_useLocalFile(lean_object*, lean_object*);
static const lean_array_object l_Lake_Artifact_trace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Artifact_trace___closed__0 = (const lean_object*)&l_Lake_Artifact_trace___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Artifact_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Artifact_trace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_artifactPath(uint64_t v_contentHash_2_, lean_object* v_ext_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_string_utf8_byte_size(v_ext_3_);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_nat_dec_eq(v___x_4_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = l_Lake_Hash_hex(v_contentHash_2_);
v___x_8_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
v___x_10_ = lean_string_append(v___x_9_, v_ext_3_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
v___x_11_ = l_Lake_Hash_hex(v_contentHash_2_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_artifactPath___boxed(lean_object* v_contentHash_12_, lean_object* v_ext_13_){
_start:
{
uint64_t v_contentHash_boxed_14_; lean_object* v_res_15_; 
v_contentHash_boxed_14_ = lean_unbox_uint64(v_contentHash_12_);
lean_dec_ref(v_contentHash_12_);
v_res_15_ = l_Lake_artifactPath(v_contentHash_boxed_14_, v_ext_13_);
lean_dec_ref(v_ext_13_);
return v_res_15_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifactDescr_default___closed__1(void){
_start:
{
lean_object* v___x_17_; uint64_t v___x_18_; lean_object* v___x_19_; 
v___x_17_ = ((lean_object*)(l_Lake_instInhabitedArtifactDescr_default___closed__0));
v___x_18_ = l_Lake_Hash_nil;
v___x_19_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_19_, 0, v___x_17_);
lean_ctor_set_uint64(v___x_19_, sizeof(void*)*1, v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifactDescr_default(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Lake_instInhabitedArtifactDescr_default___closed__1, &l_Lake_instInhabitedArtifactDescr_default___closed__1_once, _init_l_Lake_instInhabitedArtifactDescr_default___closed__1);
return v___x_20_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifactDescr(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lake_instInhabitedArtifactDescr_default;
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprArtifactDescr_repr_spec__0(lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_nat_to_int(v_a_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(8u);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(7u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__0));
v___x_49_ = lean_string_length(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__14, &l_Lake_instReprArtifactDescr_repr___redArg___closed__14_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__14);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___redArg(lean_object* v_x_56_){
_start:
{
uint64_t v_hash_57_; lean_object* v_ext_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_hash_57_ = lean_ctor_get_uint64(v_x_56_, sizeof(void*)*1);
v_ext_58_ = lean_ctor_get(v_x_56_, 0);
lean_inc_ref(v_ext_58_);
lean_dec_ref(v_x_56_);
v___x_59_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__5));
v___x_60_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__6));
v___x_61_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__7, &l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7);
v___x_62_ = l_Lake_instReprHash_repr___redArg(v_hash_57_);
v___x_63_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = 0;
v___x_65_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*1, v___x_64_);
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_60_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__9));
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_box(1);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__11));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_59_);
v___x_74_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__12, &l_Lake_instReprArtifactDescr_repr___redArg___closed__12_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__12);
v___x_75_ = l_String_quote(v_ext_58_);
v___x_76_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
v___x_77_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_74_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*1, v___x_64_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_73_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__15, &l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15);
v___x_81_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__16));
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_79_);
v___x_83_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__17));
v___x_84_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_80_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_64_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lake_instReprArtifactDescr_repr___redArg(v_x_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifactDescr_repr___boxed(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lake_instReprArtifactDescr_repr(v_x_90_, v_prec_91_);
lean_dec(v_prec_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_artifactWithExt(uint64_t v_contentHash_95_, lean_object* v_ext_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_97_, 0, v_ext_96_);
lean_ctor_set_uint64(v___x_97_, sizeof(void*)*1, v_contentHash_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_artifactWithExt___boxed(lean_object* v_contentHash_98_, lean_object* v_ext_99_){
_start:
{
uint64_t v_contentHash_boxed_100_; lean_object* v_res_101_; 
v_contentHash_boxed_100_ = lean_unbox_uint64(v_contentHash_98_);
lean_dec_ref(v_contentHash_98_);
v_res_101_ = l_Lake_artifactWithExt(v_contentHash_boxed_100_, v_ext_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath(lean_object* v_self_102_){
_start:
{
uint64_t v_hash_103_; lean_object* v_ext_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_hash_103_ = lean_ctor_get_uint64(v_self_102_, sizeof(void*)*1);
v_ext_104_ = lean_ctor_get(v_self_102_, 0);
v___x_105_ = lean_string_utf8_byte_size(v_ext_104_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_nat_dec_eq(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = l_Lake_Hash_hex(v_hash_103_);
v___x_109_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
v___x_111_ = lean_string_append(v___x_110_, v_ext_104_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = l_Lake_Hash_hex(v_hash_103_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_relPath___boxed(lean_object* v_self_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lake_ArtifactDescr_relPath(v_self_113_);
lean_dec_ref(v_self_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0(lean_object* v_x_115_){
_start:
{
uint64_t v_hash_116_; lean_object* v_ext_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_hash_116_ = lean_ctor_get_uint64(v_x_115_, sizeof(void*)*1);
v_ext_117_ = lean_ctor_get(v_x_115_, 0);
v___x_118_ = lean_string_utf8_byte_size(v_ext_117_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_dec_eq(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = l_Lake_Hash_hex(v_hash_116_);
v___x_122_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_123_ = lean_string_append(v___x_121_, v___x_122_);
v___x_124_ = lean_string_append(v___x_123_, v_ext_117_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = l_Lake_Hash_hex(v_hash_116_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToString___lam__0___boxed(lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lake_ArtifactDescr_instToString___lam__0(v_x_126_);
lean_dec_ref(v_x_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0(lean_object* v_x_130_){
_start:
{
uint64_t v_hash_131_; lean_object* v_ext_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_hash_131_ = lean_ctor_get_uint64(v_x_130_, sizeof(void*)*1);
v_ext_132_ = lean_ctor_get(v_x_130_, 0);
v___x_133_ = lean_string_utf8_byte_size(v_ext_132_);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_nat_dec_eq(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = l_Lake_Hash_hex(v_hash_131_);
v___x_137_ = ((lean_object*)(l_Lake_artifactPath___closed__0));
v___x_138_ = lean_string_append(v___x_136_, v___x_137_);
v___x_139_ = lean_string_append(v___x_138_, v_ext_132_);
v___x_140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l_Lake_Hash_hex(v_hash_131_);
v___x_142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_instToJson___lam__0___boxed(lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lake_ArtifactDescr_instToJson___lam__0(v_x_143_);
lean_dec_ref(v_x_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(lean_object* v___x_147_, lean_object* v_s_148_, lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v_startInclusive_151_; lean_object* v_endExclusive_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_startInclusive_151_ = lean_ctor_get(v___x_147_, 1);
v_endExclusive_152_ = lean_ctor_get(v___x_147_, 2);
v___x_153_ = lean_nat_sub(v_endExclusive_152_, v_startInclusive_151_);
v___x_154_ = lean_nat_dec_eq(v_a_149_, v___x_153_);
lean_dec(v___x_153_);
if (v___x_154_ == 0)
{
uint32_t v___x_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_155_ = lean_string_utf8_get_fast(v_s_148_, v_a_149_);
v___x_156_ = 46;
v___x_157_ = lean_uint32_dec_eq(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_box(0);
v___x_159_ = lean_string_utf8_next_fast(v_s_148_, v_a_149_);
lean_dec(v_a_149_);
v_a_149_ = v___x_159_;
v_b_150_ = v___x_158_;
goto _start;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v_a_149_);
return v___x_161_;
}
}
else
{
lean_dec(v_a_149_);
lean_inc(v_b_150_);
return v_b_150_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg___boxed(lean_object* v___x_162_, lean_object* v_s_163_, lean_object* v_a_164_, lean_object* v_b_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(v___x_162_, v_s_163_, v_a_164_, v_b_165_);
lean_dec(v_b_165_);
lean_dec_ref(v_s_163_);
lean_dec_ref(v___x_162_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object* v_path_171_){
_start:
{
lean_object* v___y_173_; lean_object* v_searcher_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_searcher_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_string_utf8_byte_size(v_path_171_);
lean_inc_ref(v_path_171_);
v___x_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_207_, 0, v_path_171_);
lean_ctor_set(v___x_207_, 1, v_searcher_205_);
lean_ctor_set(v___x_207_, 2, v___x_206_);
v___x_208_ = lean_box(0);
v___x_209_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(v___x_207_, v_path_171_, v_searcher_205_, v___x_208_);
lean_dec_ref(v___x_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
v___y_173_ = v___x_206_;
goto v___jp_172_;
}
else
{
lean_object* v_val_210_; 
v_val_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref(v___x_209_);
v___y_173_ = v_val_210_;
goto v___jp_172_;
}
v___jp_172_:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_string_utf8_byte_size(v_path_171_);
v___x_175_ = lean_nat_dec_eq(v___y_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_string_utf8_extract(v_path_171_, v___x_176_, v___y_173_);
v___x_178_ = l_Lake_Hash_ofHex_x3f(v___x_177_);
lean_dec_ref(v___x_177_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_190_; 
v_val_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_190_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v_ext_184_; lean_object* v___x_185_; uint64_t v___x_186_; lean_object* v___x_188_; 
v___x_183_ = lean_string_utf8_next_fast(v_path_171_, v___y_173_);
lean_dec(v___y_173_);
v_ext_184_ = lean_string_utf8_extract(v_path_171_, v___x_183_, v___x_174_);
lean_dec_ref(v_path_171_);
v___x_185_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_185_, 0, v_ext_184_);
v___x_186_ = lean_unbox_uint64(v_val_179_);
lean_dec(v_val_179_);
lean_ctor_set_uint64(v___x_185_, sizeof(void*)*1, v___x_186_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_185_);
v___x_188_ = v___x_181_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_185_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v___x_191_; 
lean_dec(v___x_178_);
lean_dec(v___y_173_);
lean_dec_ref(v_path_171_);
v___x_191_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1));
return v___x_191_;
}
}
else
{
lean_object* v___x_192_; 
lean_dec(v___y_173_);
v___x_192_ = l_Lake_Hash_ofHex_x3f(v_path_171_);
lean_dec_ref(v_path_171_);
if (lean_obj_tag(v___x_192_) == 1)
{
lean_object* v_val_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_203_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_203_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_val_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; uint64_t v___x_199_; lean_object* v___x_201_; 
v___x_197_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2));
v___x_198_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___x_199_ = lean_unbox_uint64(v_val_193_);
lean_dec(v_val_193_);
lean_ctor_set_uint64(v___x_198_, sizeof(void*)*1, v___x_199_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_198_);
v___x_201_ = v___x_195_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_198_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec(v___x_192_);
v___x_204_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__1));
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(lean_object* v___x_211_, lean_object* v_s_212_, lean_object* v_inst_213_, lean_object* v_R_214_, lean_object* v_a_215_, lean_object* v_b_216_, lean_object* v_c_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___redArg(v___x_211_, v_s_212_, v_a_215_, v_b_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0___boxed(lean_object* v___x_219_, lean_object* v_s_220_, lean_object* v_inst_221_, lean_object* v_R_222_, lean_object* v_a_223_, lean_object* v_b_224_, lean_object* v_c_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ArtifactDescr_ofFilePath_x3f_spec__0(v___x_219_, v_s_220_, v_inst_221_, v_R_222_, v_a_223_, v_b_224_, v_c_225_);
lean_dec(v_b_224_);
lean_dec_ref(v_s_220_);
lean_dec_ref(v___x_219_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object* v_data_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Json_getStr_x3f(v_data_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_239_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_239_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = ((lean_object*)(l_Lake_ArtifactDescr_fromJson_x3f___closed__0));
v___x_235_ = lean_string_append(v___x_234_, v_a_230_);
lean_dec(v_a_230_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_241_; 
v_a_240_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_240_);
lean_dec_ref(v___x_229_);
v___x_241_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_a_240_);
return v___x_241_;
}
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default___closed__0(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_to_int(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default___closed__1(void){
_start:
{
uint32_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = 0;
v___x_247_ = lean_obj_once(&l_Lake_instInhabitedArtifact_default___closed__0, &l_Lake_instInhabitedArtifact_default___closed__0_once, _init_l_Lake_instInhabitedArtifact_default___closed__0);
v___x_248_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set_uint32(v___x_248_, sizeof(void*)*1, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default___closed__2(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = lean_obj_once(&l_Lake_instInhabitedArtifact_default___closed__1, &l_Lake_instInhabitedArtifact_default___closed__1_once, _init_l_Lake_instInhabitedArtifact_default___closed__1);
v___x_250_ = ((lean_object*)(l_Lake_ArtifactDescr_ofFilePath_x3f___closed__2));
v___x_251_ = lean_obj_once(&l_Lake_instInhabitedArtifactDescr_default___closed__1, &l_Lake_instInhabitedArtifactDescr_default___closed__1_once, _init_l_Lake_instInhabitedArtifactDescr_default___closed__1);
v___x_252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
lean_ctor_set(v___x_252_, 2, v___x_250_);
lean_ctor_set(v___x_252_, 3, v___x_249_);
return v___x_252_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact_default(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&l_Lake_instInhabitedArtifact_default___closed__2, &l_Lake_instInhabitedArtifact_default___closed__2_once, _init_l_Lake_instInhabitedArtifact_default___closed__2);
return v___x_253_;
}
}
static lean_object* _init_l_Lake_instInhabitedArtifact(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lake_instInhabitedArtifact_default;
return v___x_254_;
}
}
static lean_object* _init_l_Lake_instReprArtifact_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(9u);
v___x_265_ = lean_nat_to_int(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___redArg(lean_object* v_x_278_){
_start:
{
lean_object* v_descr_279_; lean_object* v_path_280_; lean_object* v_name_281_; lean_object* v_mtime_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_descr_279_ = lean_ctor_get(v_x_278_, 0);
lean_inc_ref(v_descr_279_);
v_path_280_ = lean_ctor_get(v_x_278_, 1);
lean_inc_ref(v_path_280_);
v_name_281_ = lean_ctor_get(v_x_278_, 2);
lean_inc_ref(v_name_281_);
v_mtime_282_ = lean_ctor_get(v_x_278_, 3);
lean_inc_ref(v_mtime_282_);
lean_dec_ref(v_x_278_);
v___x_283_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__5));
v___x_284_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__3));
v___x_285_ = lean_obj_once(&l_Lake_instReprArtifact_repr___redArg___closed__4, &l_Lake_instReprArtifact_repr___redArg___closed__4_once, _init_l_Lake_instReprArtifact_repr___redArg___closed__4);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = l_Lake_instReprArtifactDescr_repr___redArg(v_descr_279_);
v___x_288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = 0;
v___x_290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v___x_289_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_284_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__9));
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_box(1);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__6));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_283_);
v___x_299_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__7, &l_Lake_instReprArtifactDescr_repr___redArg___closed__7_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__7);
v___x_300_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__8));
v___x_301_ = l_String_quote(v_path_280_);
v___x_302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_300_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = l_Repr_addAppParen(v___x_303_, v___x_286_);
v___x_305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_299_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*1, v___x_289_);
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_298_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_292_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_294_);
v___x_310_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__10));
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_283_);
v___x_313_ = l_String_quote(v_name_281_);
v___x_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___x_315_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_299_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_289_);
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_312_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_292_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_294_);
v___x_320_ = ((lean_object*)(l_Lake_instReprArtifact_repr___redArg___closed__12));
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_283_);
v___x_323_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_282_);
lean_dec_ref(v_mtime_282_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_285_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*1, v___x_289_);
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_322_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_obj_once(&l_Lake_instReprArtifactDescr_repr___redArg___closed__15, &l_Lake_instReprArtifactDescr_repr___redArg___closed__15_once, _init_l_Lake_instReprArtifactDescr_repr___redArg___closed__15);
v___x_328_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__16));
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_326_);
v___x_330_ = ((lean_object*)(l_Lake_instReprArtifactDescr_repr___redArg___closed__17));
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_327_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*1, v___x_289_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr(lean_object* v_x_334_, lean_object* v_prec_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lake_instReprArtifact_repr___redArg(v_x_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprArtifact_repr___boxed(lean_object* v_x_337_, lean_object* v_prec_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lake_instReprArtifact_repr(v_x_337_, v_prec_338_);
lean_dec(v_prec_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Artifact_withName(lean_object* v_name_342_, lean_object* v_self_343_){
_start:
{
lean_object* v_descr_344_; lean_object* v_path_345_; lean_object* v_mtime_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_descr_344_ = lean_ctor_get(v_self_343_, 0);
v_path_345_ = lean_ctor_get(v_self_343_, 1);
v_mtime_346_ = lean_ctor_get(v_self_343_, 3);
v_isSharedCheck_353_ = !lean_is_exclusive(v_self_343_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v_self_343_, 2);
lean_dec(v_unused_354_);
v___x_348_ = v_self_343_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_mtime_346_);
lean_inc(v_path_345_);
lean_inc(v_descr_344_);
lean_dec(v_self_343_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 2, v_name_342_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_descr_344_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_path_345_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_name_342_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_mtime_346_);
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
LEAN_EXPORT lean_object* l_Lake_Artifact_useLocalFile(lean_object* v_path_355_, lean_object* v_self_356_){
_start:
{
lean_object* v_descr_357_; lean_object* v_mtime_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_descr_357_ = lean_ctor_get(v_self_356_, 0);
v_mtime_358_ = lean_ctor_get(v_self_356_, 3);
v_isSharedCheck_365_ = !lean_is_exclusive(v_self_356_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; lean_object* v_unused_367_; 
v_unused_366_ = lean_ctor_get(v_self_356_, 2);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_self_356_, 1);
lean_dec(v_unused_367_);
v___x_360_ = v_self_356_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_mtime_358_);
lean_inc(v_descr_357_);
lean_dec(v_self_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
lean_inc_ref(v_path_355_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 2, v_path_355_);
lean_ctor_set(v___x_360_, 1, v_path_355_);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_descr_357_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_path_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_path_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_mtime_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Artifact_trace(lean_object* v_self_370_){
_start:
{
lean_object* v_descr_371_; lean_object* v_name_372_; lean_object* v_mtime_373_; uint64_t v_hash_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_descr_371_ = lean_ctor_get(v_self_370_, 0);
v_name_372_ = lean_ctor_get(v_self_370_, 2);
v_mtime_373_ = lean_ctor_get(v_self_370_, 3);
v_hash_374_ = lean_ctor_get_uint64(v_descr_371_, sizeof(void*)*1);
v___x_375_ = ((lean_object*)(l_Lake_Artifact_trace___closed__0));
lean_inc_ref(v_mtime_373_);
lean_inc_ref(v_name_372_);
v___x_376_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_376_, 0, v_name_372_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
lean_ctor_set(v___x_376_, 2, v_mtime_373_);
lean_ctor_set_uint64(v___x_376_, sizeof(void*)*3, v_hash_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_Artifact_trace___boxed(lean_object* v_self_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lake_Artifact_trace(v_self_377_);
lean_dec_ref(v_self_377_);
return v_res_378_;
}
}
lean_object* runtime_initialize_Lake_Build_Trace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Artifact(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedArtifactDescr_default = _init_l_Lake_instInhabitedArtifactDescr_default();
lean_mark_persistent(l_Lake_instInhabitedArtifactDescr_default);
l_Lake_instInhabitedArtifactDescr = _init_l_Lake_instInhabitedArtifactDescr();
lean_mark_persistent(l_Lake_instInhabitedArtifactDescr);
l_Lake_instInhabitedArtifact_default = _init_l_Lake_instInhabitedArtifact_default();
lean_mark_persistent(l_Lake_instInhabitedArtifact_default);
l_Lake_instInhabitedArtifact = _init_l_Lake_instInhabitedArtifact();
lean_mark_persistent(l_Lake_instInhabitedArtifact);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Artifact(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Trace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Artifact(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Artifact(builtin);
}
#ifdef __cplusplus
}
#endif
