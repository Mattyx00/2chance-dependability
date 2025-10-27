package controller;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet(name = "ConfrontaServlet", value = "/ConfrontaServlet")
public class ConfrontaServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
       int id1 = Integer.parseInt(request.getParameter("prodotto1"));
       int id2 = Integer.parseInt(request.getParameter("prodotto2"));

        try {
            ProdottoDAO dao = new ProdottoDAO();
            Prodotto p1 = dao.getProdottoById(id1);
            Prodotto p2 = dao.getProdottoById(id2);

            request.setAttribute("confronto1", p1);
            request.setAttribute("confronto2", p2);

            String address = "/confronta.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);

        } catch (SQLException throwables) {
            throwables.printStackTrace();
        }

    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
