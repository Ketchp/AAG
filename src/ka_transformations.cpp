#ifndef __PROGTEST__
#include <iostream>
#include <sstream>

#include <algorithm>
#include <deque>
#include <list>
#include <map>
#include <set>
#include <vector>
#endif


namespace AAG {
    template<typename T_state_new = int>
    struct Namer {
        using T_name = T_state_new;
        T_name state{};
        T_name new_state() {return state++;}
    };

    template <typename T>
    bool have_common_element(const std::set<T> &a, const std::set<T> &b) {
        auto first1 = a.begin(), first2 = b.begin();
        const auto last1 = a.end(), last2 = b.end();

        while (first1 != last1 && first2 != last2) {
            if (*first1 < *first2)
                ++first1;
            else if (*first2 < *first1)
                ++first2;
            else
                return true;
        }
        return false;
    }

    template<typename T_symbol>
    struct EpsilonSymbol: public std::pair<T_symbol, bool> {
        using std::pair<T_symbol, bool>::pair;
        explicit EpsilonSymbol(T_symbol symbol): std::pair<T_symbol, bool>(symbol, false) {}

        static EpsilonSymbol epsilon() {
            return EpsilonSymbol();
        };

        [[nodiscard]] T_symbol remove_epsilon() const { return this->first; }

        [[nodiscard]] bool is_epsilon() const { return this->second; }

        template <typename T_s>
        friend std::ostream &operator<<(std::ostream &os, const EpsilonSymbol<T_s> &);
    private:
        EpsilonSymbol(): std::pair<T_symbol, bool>({}, true) {};
    };

    template <typename T>
    concept EpsilonSymbolLike = requires(T t) { t.is_epsilon(); };

    template <typename T_symbol>
    std::ostream &operator<<(std::ostream &os, const EpsilonSymbol<T_symbol> &symbol) {
        if(symbol.second) os << '_';
        else os << symbol.first;
        return os;
    }

    template<typename T>
    struct State_set: public std::set<T> {
        using T_self = State_set<T>;
        using std::set<T>::set;

        using std::set<T>::merge;

        void merge(const State_set &other) {
            merge(static_cast<std::set<T>>(other));
        }

        bool operator<(const T_self &o) const {
            if(this->size() < o.size()) return true;
            if(o.size() < this->size()) return false;
            return static_cast<const std::set<T> &>(*this) < (o);
        }
    };

    template<typename T_state>
    std::ostream &operator<<(std::ostream &os, const std::set<T_state> &s) {
        os << '{';
        for(auto it = s.begin();
            it != s.end() && ++it != s.end();
            it++) {
            it--;
            os << *it << ", ";
        }
        if(!s.empty())
            os << *s.rbegin();
        return os << '}';
    }

    template<typename T_state>
    using T_states = State_set<T_state>;

    template<typename T_symbol, typename T_destination>
    using T_transition = std::map<T_symbol, T_destination>;

    template<typename T_state, typename T_symbol, typename T_destination = T_state>
    using T_transitions = std::map<T_state, T_transition<T_symbol, T_destination>>;

    template<typename T_state>
    using T_start = T_states<T_state>;

    template<typename T_state>
    using T_end = T_states<T_state>;

    template<typename T_state, typename T_symbol, typename T_destination>
    class KA: public std::tuple<T_transitions<T_state, T_symbol, T_destination>,
            T_start<T_state>,
            T_end<T_state>> {
        using T_transitions_KA = T_transitions<T_state, T_symbol, T_destination>;
        using std::tuple<T_transitions_KA,
                T_start<T_state>,
                T_end<T_state>>::tuple;
    public:
        auto &
        transitions()
        { return std::get<0>(*this); };

        [[nodiscard]] const auto &
        transitions() const
        { return std::get<0>(*this); };

        auto &
        start_states()
        { return std::get<1>(*this); };

        [[nodiscard]] const auto &
        start_states() const
        { return std::get<1>(*this); };

        auto &
        end_states()
        { return std::get<2>(*this); };

        [[nodiscard]] const auto &
        end_states() const
        { return std::get<2>(*this); };

        template<typename T_S, typename T_A, typename T_D>
        friend std::ostream &operator<<(std::ostream &os, const KA<T_S, T_A, T_D> &);
    };

    template<typename T_state, typename T_symbol, typename T_dest>
    std::ostream &operator<<(std::ostream &os, const KA<T_state, T_symbol, T_dest> &ka) {
        const auto &starts = ka.start_states();
        const auto &ends = ka.end_states();
        const auto &transitions = ka.transitions();

        std::set<T_symbol> symbols;
        for(const auto &[state, trans]: transitions)
            for(const auto &[symbol, d]: trans)
                symbols.emplace(symbol);

        for(const auto &[state, trans]: transitions) {
            os << (ends.contains(state) ? '<' : ' ');
            os << '-';
            os << (starts.contains(state) ? '>' : ' ');

            os << state << "=> ";
            for(const auto &s: symbols) {
                if(!trans.contains(s))
                    continue;
                os << s << ':' << trans.at(s) << ", ";
            }

            os << '\n';
        }

        return os;
    }


    template<typename T_state, typename T_symbol>
    using T_NKA = KA<T_state, T_symbol, T_states<T_state>>;

    template<typename T_state, typename T_symbol>
    using T_DKA = KA<T_state, T_symbol, T_state>;


    template<typename T_state = int, typename T_symbol = char>
    struct NKA: public T_NKA<T_state, T_symbol> {
        using T_NKA<T_state, T_symbol>::T_NKA;
    };

    template<typename T_state, EpsilonSymbolLike T_symbol>
    struct NKAe: public NKA<T_state, T_symbol> {
        [[nodiscard]] T_states<T_state>
        epsilon_closure(
                const T_state &from_state) const
        {
            T_states<T_state> closure;
            std::set<T_state> to_do;
            to_do.emplace(from_state);
            const auto &trans = this->transitions();

            while(!to_do.empty()) {
                const auto c = to_do.extract(to_do.begin()).value();
                closure.insert(c);

                if(!trans.contains(c)) continue;
                for(const auto &[symbol, destinations]: trans.at(c)) {
                    if(!symbol.is_epsilon()) continue;
                    to_do.insert(destinations.begin(), destinations.end());
                }
            }

            return closure;
        }
    };

    template <typename G>
    concept StateGenerator = requires(G g) {
        typename G::T_name;
        { g.new_state() } -> std::same_as<typename G::T_name>;
    };

    template<typename T_state = int, typename T_symbol = char>
    struct DKA: public T_DKA<T_state, T_symbol> {
        using T_DKA<T_state, T_symbol>::T_DKA;

        template<StateGenerator G>
        DKA<typename G::T_name, T_symbol> rename_states(G g) {
            using T_state_new = G::T_name;
            DKA<T_state_new, T_symbol> renamed;

            std::map<T_state, T_state_new> mapping;
            auto get_state = [&mapping, &g](const T_state &st) {
                if(mapping.contains(st)) return mapping.at(st);
                return mapping.emplace(st, g.new_state()).first->second;
            };

            for(const auto &start: this->start_states())
                renamed.start_states().emplace(get_state(start));

            for(const auto &start: this->end_states())
                renamed.end_states().emplace(get_state(start));

            for(const auto &[state, trans]: this->transitions()){
                const auto &ns = get_state(state);
                for(const auto &[symbol, dest]: trans) {
                    renamed.transitions()[ns].emplace(symbol, get_state(dest));
                }
            }

            return renamed;
        }

    };


    template<typename T_state, typename T_symbol, typename T_state_DKA = State_set<T_state>>
    DKA<T_state_DKA, T_symbol>
    nka2dka(
            const NKA<T_state, T_symbol> &nka)
    {
        using T_state_nka = T_state;
        using T_state_dka = State_set<T_state>;

        using T_transition_dka = T_transition<T_symbol, T_state_dka>;

        const T_transitions<T_state, T_symbol, T_states<T_state>> &nka_trans = nka.transitions();
        const auto &nka_starts = nka.start_states();
        const auto &nka_ends = nka.end_states();

        T_states<T_state_dka> dka_starts;
        T_states<T_state_dka> dka_ends;

        for(T_state_nka start: nka_starts)
            dka_starts.emplace(T_state_dka{std::move(start)});

        T_transitions<T_state_dka, T_symbol> transitions_dka;

        std::vector<T_state_dka> to_process(dka_starts.begin(), dka_starts.end());

        while(!to_process.empty()) {
            T_state_dka from = std::move(to_process.back());
            to_process.pop_back();

            if(have_common_element(nka_ends, from))
                dka_ends.emplace(from);

            T_transition_dka trans_dka;

            for(const T_state_nka &from_nka: from) {
                if(!nka_trans.contains(from_nka)) continue;
                for(const auto &[symbol, dest]: nka_trans.at(from_nka)) {
                    trans_dka[symbol].insert(dest.begin(), dest.end());
                }
            }

            for(const auto &[symbol, to]: trans_dka) {
                if(from == to) continue;
                if(transitions_dka.find(to) != transitions_dka.end()) continue;
                to_process.emplace_back(to);
            }

            transitions_dka[from] = trans_dka;
        }

        return {transitions_dka, dka_starts, dka_ends};
    }

    template<typename T_state, typename T_symbol>
    NKAe<T_state, EpsilonSymbol<T_symbol>>
    remove_multiple_start(
            const NKA<T_state, T_symbol> &nka,
            T_state new_start)
    {
        NKAe<T_state, EpsilonSymbol<T_symbol>> out;
        out.end_states() = nka.end_states();

        if(nka.start_states().size() > 1){
            const auto epsilon = EpsilonSymbol<T_symbol>::epsilon();

            out.transitions()[new_start][epsilon] = nka.start_states();

            out.start_states().emplace(std::move(new_start));
        }
        else
            out.start_states() = nka.start_states();

        for(const auto &[state, trans]: nka.transitions())
            for(const auto &[symbol, destination]: trans)
                out.transitions()[state][EpsilonSymbol{symbol}] = destination;

        return out;
    }

    template<typename T_state, typename T_symbol>
    NKA<T_state, T_symbol>
    remove_epsilon(
            const NKAe<T_state, EpsilonSymbol<T_symbol>> &nka_e)
    {
        NKA<T_state, T_symbol> out;
        const auto &in_trans = nka_e.transitions();
        auto &out_trans = out.transitions();

        out.start_states() = nka_e.start_states();
        out.end_states() = nka_e.end_states();

        for(const auto &[state, trans]: in_trans) {
            for(const auto &[e_symbol, dest]: trans) {
                if(!e_symbol.is_epsilon())
                    out_trans[state][e_symbol.remove_epsilon()] = dest;
            }
            const auto closure = nka_e.epsilon_closure(state);
            if(have_common_element(closure, nka_e.end_states())) {
                out.end_states().emplace(state);
            }

            for(const auto &ng_state: closure) {
                if(!in_trans.contains(ng_state))
                    continue;
                for(const auto &[symbol, dest]: in_trans.at(ng_state)) {
                    if(symbol.is_epsilon()) continue;
                    out_trans[state][symbol.remove_epsilon()].merge(dest);
                }
            }
        }

        return out;
    }

    template<typename T_state, typename T_symbol>
    NKA<T_state, T_symbol> NKA_reverse(const NKA<T_state, T_symbol> &orig) {
        NKA<T_state, T_symbol> reversed;

        const auto &ot = orig.transitions();
        auto &rt = reversed.transitions();

        reversed.end_states() = orig.start_states();

        std::vector<T_state> to_do(orig.start_states().begin(),
                                   orig.start_states().end());
        std::set<T_state> done;

        while(!to_do.empty()) {
            const auto current = to_do.back();
            done.emplace(current);
            to_do.pop_back();

            if(orig.end_states().contains(current))
                reversed.start_states().emplace(current);

            if(!ot.contains(current))
                continue;

            for(const auto &[symbol, destinations]: ot.at(current))
                for(const auto &dest: destinations) {
                    rt[dest][symbol].emplace(current);
                    if(!done.contains(dest))
                        to_do.emplace_back(dest);
                }
        }
        return reversed;
    }

    template<typename T_state, typename T_symbol>
    NKA<T_state, T_symbol>
    NKA_remove_useless_unreachable(const NKA<T_state, T_symbol> &orig) {
        return NKA_reverse(NKA_reverse(orig));
    }
}


namespace AAG_symbols {
    enum class State: unsigned int {};
    enum class Symbol: char {};

    std::ostream &operator<<(std::ostream &os, const State &s) {
        return os << static_cast<std::underlying_type_t<const State>>(s);
    }

    std::ostream &operator<<(std::ostream &os, const Symbol &s) {
        return os << static_cast<char>(s);
    }
}
