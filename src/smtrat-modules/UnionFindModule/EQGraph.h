/**
 * @file EQGraph.h
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#pragma once

#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/breadth_first_search.hpp>

enum vertex_properties_t { vertex_properties };

namespace boost {
    BOOST_INSTALL_PROPERTY(vertex, properties);
}

namespace smtrat
{

    template< typename VertexName >
    struct EQGraph
    {
        using vec = boost::vecS;
        using undirected = boost::undirectedS;
        using vertex_property = boost::property<vertex_properties_t, VertexName>;

        using Graph = boost::adjacency_list<vec, vec, undirected, vertex_property>;
        using Vertex = typename boost::graph_traits<Graph>::vertex_descriptor;

        auto properties() noexcept { return get(vertex_properties, graph); }
        auto properties() const noexcept { return get(vertex_properties, graph); }

        VertexName const& properties(Vertex const& v) const noexcept
        {
            return properties()[v];
        }

        VertexName & properties(Vertex const& v) noexcept
        {
            return properties()[v];
        }

        void add_vertex(VertexName const& name) noexcept
        {
            auto v = boost::add_vertex(graph);
            properties(v) = name;
            vertices.emplace(name, v);
        }

        void add_edge(VertexName const& a, VertexName const& b) noexcept
        {
            boost::add_edge(vertices.at(a), vertices.at(b), graph);
        }

        void remove_edge(VertexName const& a, VertexName const& b) noexcept
        {
            boost::remove_edge(vertices.at(a), vertices.at(b), graph);
        }

        using PathEdge = std::pair<VertexName, VertexName>;
        std::vector<PathEdge> get_path(VertexName const& a, VertexName const& b) noexcept
        {
            const auto& begin = vertices.at(a);
            const auto& end = vertices.at(b);

            assert( a != b );

            std::vector<Vertex> predecessors(vertices.size(), Graph::null_vertex());

            boost::breadth_first_search(graph, begin,
                boost::visitor(boost::make_bfs_visitor(
                    boost::record_predecessors(predecessors.data(), boost::on_tree_edge{})
            )));

            std::vector<PathEdge> path;
            auto prop = properties();

            int vertex = end;
            while (vertex != begin) {
                auto next = predecessors[vertex];
                assert( next != Graph::null_vertex() );

                path.emplace_back(prop[vertex], prop[next]);
                vertex = next;
            }

            return path;
        }

        Graph graph;
        std::map<VertexName, Vertex> vertices;
    };
} // namespace smtrat
