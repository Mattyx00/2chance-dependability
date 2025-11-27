package controller;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "landingpage", value = "/landingpage", loadOnStartup = 1)
public class landingpage extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            ProdottoDAO dao = new ProdottoDAO();
            ArrayList<Prodotto> prodotti = dao.getUltimiProdotti();
            request.setAttribute("prodotti", prodotti);

           /*
            for(Prodotto e: prodotti ){
                System.out.println(e.getCategoria().getNomeCategoria());
            }
            */

        } catch (SQLException e) {
            e.printStackTrace();
        }

        String address = "/index.jsp";
        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        dispatcher.forward(request, response);

    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
