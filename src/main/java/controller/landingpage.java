package controller;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.dao.CategoriaDAO;
import model.dao.ProdottoDAO;
import org.json.JSONArray;
import org.json.JSONObject;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Enumeration;

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
