
/***************************************************************************
 *  clips_pddl_parser.cpp - Parse PDDL files to a CLIPS environment
 *
 *  Created: Tue Apr 16 13:51:14 2013
 *  Copyright  2013  Tim Niemueller [www.niemueller.de]
 *             2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 ****************************************************************************/

/*  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 * - Redistributions of source code must retain the above copyright
 *   notice, this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright
 *   notice, this list of conditions and the following disclaimer in
 *   the documentation and/or other materials provided with the
 *   distribution.
 * - Neither the name of the authors nor the names of its contributors
 *   may be used to endorse or promote products derived from this
 *   software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <clips_pddl_parser/clips_pddl_parser.h>
#include <clips_pddl_parser/effect_visitor.h>
#include <clips_pddl_parser/precondition_visitor.h>
#include <pddl_parser/pddl_parser.h>
#include <spdlog/spdlog.h>

#include <clipsmm.h>
#include <fstream>

using namespace std;
using namespace pddl_parser;

namespace clips_pddl_parser {

/** @class ClipsPddlParser <clips_pddl_parser/communicator.h>
 * CLIPS protobuf integration class.
 * This class adds functionality related to protobuf to a given CLIPS
 * environment. It supports the creation of communication channels
 * through protobuf_comm. An instance maintains its own message register
 * shared among server, peer, and clients.
 * @author Tim Niemueller
 */

/** Constructor.
 * @param env CLIPS environment to which to provide the protobuf functionality
 * @param env_mutex mutex to lock when operating on the CLIPS environment.
 */
ClipsPddlParser::ClipsPddlParser(CLIPS::Environment *env, std::mutex &env_mutex)
: clips_(env), clips_mutex_(env_mutex)
{
	setup_clips();
}

/** Destructor. */
ClipsPddlParser::~ClipsPddlParser()
{
	{
		std::lock_guard<std::mutex> lock(clips_mutex_);

		for (auto f : functions_) {
			clips_->remove_function(f);
		}
		functions_.clear();
	}
}

#define ADD_FUNCTION(n, s)    \
	clips_->add_function(n, s); \
	functions_.push_back(n);

/** Setup CLIPS environment. */
void
ClipsPddlParser::setup_clips()
{
	std::lock_guard<std::mutex> lock(clips_mutex_);
	ADD_FUNCTION("parse-pddl-domain",
	                    (sigc::slot<void, string>(
	                      sigc::mem_fun(*this, &ClipsPddlParser::parse_domain))));
}
/** CLIPS function to parse a PDDL domain.
 * This parses the given domain and asserts domain facts for all parts of the
 * domain.
 * @param env_name The name of the calling environment
 * @param domain_file The path of the domain file to parse.
 */
void
ClipsPddlParser::parse_domain(std::string env_name, std::string domain_file) {
	Domain              domain;
	try {
		ifstream     df(domain_file);
		stringstream buffer;
		buffer << df.rdbuf();
		domain = PddlParser::parseDomain(buffer.str());
	} catch (PddlParserException &e) {
		SPDLOG_WARN(std::string("CLIPS_PDDL_Parser: Failed to parse domain:") + e.what());
		return;
	}
	std::lock_guard<std::mutex> lock(clips_mutex_);
	for (auto &type : domain.types) {
		string super_type = "";
		if (!type.second.empty()) {
			super_type = "(super-type " + type.second + ")";
		}
		env.assert_fact("(domain-object-type "
		                "(name "
		                + type.first + ")" + super_type + ")");
	}
	for (auto &predicate : domain.predicates) {
		string param_string = "";
		string type_string  = "";
		for (auto &param : predicate.second) {
			param_string += " " + param.first;
			type_string += " " + param.second;
		}
		env.assert_fact("(domain-predicate"
		                " (name "
		                + predicate.first
		                + ")"
		                  " (param-names "
		                + param_string
		                + ")"
		                  " (param-types "
		                + type_string
		                + ")"
		                  ")");
	}

	for (auto &action : domain.actions) {
		string params_string = "(param-names";
		for (auto &param_pair : action.action_params) {
			string param_name = param_pair.first;
			string param_type = param_pair.second;
			params_string += " " + param_name;
			env.assert_fact("(domain-operator-parameter"
			                " (name "
			                + param_name
			                + ")"
			                  " (operator "
			                + action.name
			                + ")"
			                  " (type "
			                + param_type
			                + ")"
			                  ")");
		}
		params_string += ")";
		env.assert_fact("(domain-operator (name " + action.name + ")" + params_string + ")");
		vector<string> precondition_facts =
		  boost::apply_visitor(PreconditionToCLIPSFactVisitor(action.name, 1, true),
		                       action.precondition.expression);
		for (auto &fact : precondition_facts) {
			env.assert_fact(fact);
		}
		vector<string> effect_facts =
		  boost::apply_visitor(EffectToCLIPSFactVisitor(action.name, true), action.effect.expression);
		for (auto &fact : effect_facts) {
			env.assert_fact(fact);
		}
	}

} // end namespace clips_pddl_parser
