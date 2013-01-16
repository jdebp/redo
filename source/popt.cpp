/* COPYING ******************************************************************
For copyright and licensing terms, see the file named COPYING.
// **************************************************************************
*/

#include <iostream>
#include <iomanip>
#include <cstring>
#include <cstdlib>
#include <cctype>

#include "popt.h"

using namespace popt;

processor::processor(const char * n, definition & d, std::vector<const char *> & f) :
	file_vector(f), name(n), slash(0), def(d), is_stopped(false)
{
}
definition::~definition() {}
named_definition::~named_definition() {}
simple_named_definition::~simple_named_definition() {}
bool simple_named_definition::execute(processor & proc, char c)
{
	if (char short_name = query_short_name()) {
		if (short_name == c) {
			action(proc);
			return true;
		}
	}
	return false;
}
bool simple_named_definition::execute(processor &, char, const char *)
{
	return false;
}
bool simple_named_definition::execute(processor & proc, const char * s)
{
	if (const char * long_name = query_long_name()) {
		if (0 == std::strcmp(long_name, s)) {
			action(proc);
			return true;
		}
	}
	return false;
}
compound_named_definition::~compound_named_definition() {}
bool compound_named_definition::execute(processor & proc, char c)
{
	if (char short_name = query_short_name()) {
		if (short_name == c) {
			if (const char * text = proc.next_arg()) {
				action(proc, text);
				return true;
			} else
				throw error(long_name, "missing option argument");
		}
	}
	return false;
}
bool compound_named_definition::execute(processor & proc, char c, const char * text)
{
	if (!*text) return false;
	if (char short_name = query_short_name()) {
		if (short_name == c) {
			action(proc, text);
			return true;
		}
	}
	return false;
}
bool compound_named_definition::execute(processor & proc, const char * s)
{
	if (const char * long_name = query_long_name()) {
		if (0 == std::strcmp(long_name, s)) {
			if (const char * text = proc.next_arg()) {
				action(proc, text);
				return true;
			} else
				throw error(long_name, "missing option argument");
		}
	}
	return false;
}
string_definition::~string_definition() {}
void string_definition::action(processor &, const char * text)
{
	value = text;
}
string_list_definition::~string_list_definition() {}
void string_list_definition::action(processor &, const char * text)
{
	value_list.push_back(text);
}
bool_definition::~bool_definition() {}
void bool_definition::action(processor & /*proc*/)
{
	value = true;
}
signed_number_definition::~signed_number_definition() {}
void signed_number_definition::action(processor &, const char * text)
{
	const char * old(text);
	value = std::strtol(text, const_cast<char **>(&text), base);
	if (text == old || *text)
		throw error(old, "not a number");
	set = true;
}
unsigned_number_definition::~unsigned_number_definition() {}
void unsigned_number_definition::action(processor &, const char * text)
{
	const char * old(text);
	value = std::strtoul(text, const_cast<char **>(&text), base);
	if (text == old || *text)
		throw error(old, "not a number");
	set = true;
}
table_definition::~table_definition() {}
bool table_definition::execute(processor & proc, char c)
{
	for (unsigned i(0); i < count; ++i)
		if (array[i]->execute(proc, c))
			return true;
	return false;
}
bool table_definition::execute(processor & proc, char c, const char * s)
{
	for (unsigned i(0); i < count; ++i)
		if (array[i]->execute(proc, c, s))
			return true;
	return false;
}
bool table_definition::execute(processor & proc, const char * s)
{
	for (unsigned i(0); i < count; ++i)
		if (array[i]->execute(proc, s))
			return true;
	return false;
}
void table_definition::help()
{
	std::clog << description << ":\n";
	std::size_t w = 0;
	for (unsigned i(0); i < count; ++i)
		if (named_definition * n = dynamic_cast<named_definition *>(array[i])) {
			std::size_t l = 0;
			if (char short_name = n->query_short_name()) l += 2;
			if (const char * long_name = n->query_long_name()) {
				if (char short_name = n->query_short_name()) l += 1;
				l += 2 + std::strlen(long_name);
			}
			if (const char * args_description = n->query_args_description())
				l += 1 + std::strlen(args_description);
			if (l > w) w = l;
		}
	for (unsigned i(0); i < count; ++i)
		if (named_definition * n = dynamic_cast<named_definition *>(array[i])) {
			std::string t;
			if (char short_name = n->query_short_name())
				t += "-" + std::string(1, short_name);
			if (const char * long_name = n->query_long_name()) {
				if (char short_name = n->query_short_name()) t += "|";
				t += "--" + std::string(long_name);
			}
			if (const char * args_description = n->query_args_description())
				t += " " + std::string(args_description);
			std::clog.put('\t') << std::setiosflags(std::iostream::left) << std::setw(static_cast<int>(w))
#if defined(__WATCOMC__) // Watcom C++ library bug: std::strings are not output as one lump
			<< t.c_str()
#else
			<< t
#endif
			;
			if (const char * entry_description = n->query_description())
				std::clog.put(' ') << entry_description;
			std::clog.put('\n');
		}
	for (unsigned i(0); i < count; ++i)
		if (table_definition * n = dynamic_cast<table_definition *>(array[i]))
			n->help();
}
void table_definition::long_usage()
{
	for (unsigned i(0); i < count; ++i)
		if (named_definition * n = dynamic_cast<named_definition *>(array[i])) {
			const char * args = n->query_args_description();
			char short_name = n->query_short_name();
			const char * long_name = n->query_long_name();
			std::clog << "[";
			if (args && short_name) {
				std::clog.put('-').put(short_name);
				if (long_name) std::clog.put('|');
			}
			if (long_name)
				std::clog << "--" << long_name;
			if (args) std::clog << " " << args;
			std::clog << "] ";
		}
	for (unsigned i(0); i < count; ++i)
		if (table_definition * n = dynamic_cast<table_definition *>(array[i]))
			n->long_usage();
}
void table_definition::gather_combining_shorts(std::string & shorts)
{
	for (unsigned i(0); i < count; ++i)
		if (named_definition * n = dynamic_cast<named_definition *>(array[i])) {
			if (!n->query_args_description()) {
				if (char short_name = n->query_short_name())
					shorts += short_name;
			}
		}
	for (unsigned i(0); i < count; ++i)
		if (table_definition * n = dynamic_cast<table_definition *>(array[i]))
			n->gather_combining_shorts(shorts);
}
top_table_definition::~top_table_definition() {}
bool top_table_definition::execute(processor & proc, char c)
{
	if ('?' == c) { do_help(proc); return true; }
	return table_definition::execute(proc, c);
}
bool top_table_definition::execute(processor & proc, const char * s)
{
	if (0 == std::strcmp(s, "help")) { do_help(proc); return true; }
	if (0 == std::strcmp(s, "usage")) { do_usage(proc); return true; }
	return table_definition::execute(proc, s);
}
void top_table_definition::do_usage(processor & proc)
{
	std::string shorts("?");
	gather_combining_shorts(shorts);
	std::clog << "Usage: " << proc.name << " [-" << shorts << "] [--help] [--usage] ";
	long_usage();
	std::clog << arguments_description << '\n';
	proc.stop();
}
void top_table_definition::do_help(processor & proc)
{
	do_usage(proc);
	std::clog.put('\n');
	help();
	proc.stop();
}
